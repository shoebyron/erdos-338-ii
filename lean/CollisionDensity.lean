import BoundedByOrderFixed
import DensityPartners

/-! A finite comparison between ordinary and distinct sums, followed by the
uniform-density deduction. The replacement/forbidden-partner method follows
Hegyvári–Hennecart–Plagne and the public #339 formalization by plby/lean-proofs.
For sums of at most h terms it suffices to track the number of repetitions.
We may use a fixed pool of h+1 summands from A at every window size.
-/ 

namespace Erdos338.Bridge

open Filter
open scoped Classical BigOperators

/-- At most h summands, and at most d occurrences beyond the first occurrence of each value. -/
def CollisionRep (A : Set ℕ) (h d n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ a ∈ s, a ∈ A) ∧ s.card ≤ h ∧
    s.card ≤ s.toFinset.card + d ∧ s.sum = n

noncomputable def collisionWindow (A : Set ℕ) (h d N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (CollisionRep A h d)

private theorem duplicate_cons {s : Multiset ℕ} (hn : ¬s.Nodup) :
    ∃ a t, s = a ::ₘ t ∧ a ∈ t := by
  rw [Multiset.nodup_iff_count_le_one] at hn
  push Not at hn
  obtain ⟨a, ha⟩ := hn
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem (Multiset.count_pos.mp (Nat.zero_lt_of_lt ha))
  refine ⟨a, t, rfl, Multiset.count_pos.mp ?_⟩
  simpa using ha

private def PartialRep (A : Set ℕ) (h d b : ℕ) (t : Multiset ℕ) : Prop :=
  (∀ a ∈ t, a ∈ A) ∧ t.card < h ∧ t.card ≤ t.toFinset.card + d ∧ t.sum = b

/-- Adding a fresh partner preserves the collision budget. -/
private theorem append_fresh {A : Set ℕ} {h d b a : ℕ} {t : Multiset ℕ}
    (ht : PartialRep A h d b t) (ha : a ∈ A) (hf : a ∉ t.toFinset) :
    CollisionRep A h d (b + a) := by
  obtain ⟨hA, hlen, hcol, hsum⟩ := ht
  refine ⟨a ::ₘ t, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | h
    · exact ha
    · exact hA _ h
  · simp only [Multiset.card_cons]; omega
  · rw [Multiset.card_cons, Multiset.toFinset_cons, Finset.card_insert_of_notMem hf]
    omega
  · simp [hsum, Nat.add_comm]

/-- Removing a repeated summand from a non-distinct representation drops its
collision budget by one without losing the value from its support. -/
private theorem split_collision {A : Set ℕ} {h d n : ℕ}
    (hs : CollisionRep A h (d+1) n) :
    CollisionRep A h d n ∨ ∃ b a t, PartialRep A h d b t ∧ a ∈ A ∧ b + a = n := by
  obtain ⟨s, hA, hlen, hcol, hsum⟩ := hs
  by_cases hn : s.Nodup
  · exact Or.inl ⟨s, hA, hlen, by rw [Multiset.toFinset_card_of_nodup hn]; omega, hsum⟩
  · obtain ⟨a, t, rfl, hat⟩ := duplicate_cons hn
    have haT : a ∈ t.toFinset := Multiset.mem_toFinset.mpr hat
    simp only [Multiset.card_cons, Multiset.toFinset_cons, Finset.insert_eq_of_mem haT] at hlen hcol
    refine Or.inr ⟨t.sum, a, t, ⟨fun x hx => hA x (Multiset.mem_cons_of_mem hx), by omega, by omega, rfl⟩,
      hA a (Multiset.mem_cons_self a t), ?_⟩
    simpa [Nat.add_comm] using hsum

/-- The one-step window comparison. The shift U may depend on A, but the
multiplicative constant depends only on the number of partners and on h. -/
theorem collisionWindow_step (A : Set ℕ) (h d N U : ℕ) (T : Finset ℕ)
    (hT : h < T.card) (hTA : ∀ a ∈ T, a ∈ A) (hU : ∀ a ∈ T, a ≤ U) :
    (collisionWindow A h (d+1) N).card ≤
      (1 + h*T.card) * (collisionWindow A h d (N+U)).card := by
  classical
  let G := collisionWindow A h d (N + U)
  let B := (Finset.range N).filter (fun b => ∃ t, PartialRep A h d b t)
  let t (b : ℕ) : Multiset ℕ :=
    if ex : ∃ s, PartialRep A h d b s then ex.choose else 0
  have chosen {b : ℕ} (hb : b ∈ B) : PartialRep A h d b (t b) := by
    have ex := (Finset.mem_filter.mp hb).2
    simpa only [t, dite_eq_left ex] using ex.choose_spec
  let F (b : ℕ) := (t b).toFinset
  have hsize (b : ℕ) (hb : b ∈ B) : (F b).card ≤ h :=
    (t b).toFinset_card_le.trans (chosen hb).2.1.le
  have allowed {b a : ℕ} (hb : b ∈ B) (ha : a ∈ A) (hf : a ∉ F b) (hn : b + a < N + U) :
      b + a ∈ G :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, append_fresh (chosen hb) ha hf⟩
  have bound := exceptionalPartnerCount B T G F h hsize hT (by
    intro b hb a hat hf
    have hbN := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have haU := hU a hat
    apply allowed hb (hTA a hat) hf
    omega)
  have sub : collisionWindow A h (d+1) N ⊆ G ∪ B.biUnion (fun b => (F b).image (fun a => b+a)) := by
    intro n hn
    obtain ⟨hnN, hrep⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hnN
    rcases split_collision hrep with hgood | ⟨b, a, s, hs, haA, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hgood⟩)
    · have hb : b ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), s, hs⟩
      by_cases hf : a ∈ F b
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨a, hf, rfl⟩⟩)
      · exact Finset.mem_union_left _ (allowed hb haA hf (by omega))
  calc
    _ ≤ (G ∪ B.biUnion (fun b => (F b).image (fun a => b+a))).card := Finset.card_le_card sub
    _ ≤ G.card + _ := Finset.card_union_le _ _
    _ ≤ G.card + h*T.card*G.card := Nat.add_le_add_left bound _
    _ = (1 + h*T.card) * G.card := by ring

/-- Iterating eliminates every repeated occurrence. The accumulated shift is
additive while the coefficient depends only on h and the pool cardinality. -/
theorem collisionWindow_iterate (A : Set ℕ) (h d N U : ℕ) (T : Finset ℕ)
    (hT : h < T.card) (hTA : ∀ a ∈ T, a ∈ A) (hU : ∀ a ∈ T, a ≤ U) :
    (collisionWindow A h d N).card ≤
      (1 + h * T.card)^d * (collisionWindow A h 0 (N + d*U)).card := by
  induction d generalizing N with
  | zero => simp
  | succ d ih =>
    calc
      _ ≤ _ := collisionWindow_step A h d N U T hT hTA hU
      _ ≤ (1+h*T.card) * ((1+h*T.card)^d * (collisionWindow A h 0 (N+U+d*U)).card) :=
        Nat.mul_le_mul_left _ (ih (N+U))
      _ = _ := by
        rw [show N+U+d*U = N+(d+1)*U by ring, pow_succ]
        ring

private theorem hasOrder_infinite {A : Set ℕ} {h : ℕ} (hA : HasOrder A h) : A.Infinite := by
  intro hfin
  obtain ⟨V, hV⟩ := hfin.bddAbove
  obtain ⟨n, ⟨s, hs, hc, he⟩, hn⟩ := (hA.and (eventually_gt_atTop (h * V))).exists
  have total (t : Multiset ℕ) (ht : ∀ x ∈ t, x ≤ V) : t.sum ≤ t.card * V := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons x t ih =>
      have hrest := ih (fun y hy => ht y (Multiset.mem_cons_of_mem hy))
      have hx := ht x (Multiset.mem_cons_self x t)
      simp only [Multiset.sum_cons, Multiset.card_cons, Nat.succ_mul]
      omega
  have hsum := total s (fun x hx => hV (hs x hx))
  exact (not_le_of_gt hn) (he ▸ (hsum.trans (Nat.mul_le_mul_right V hc)))

private theorem collision_zero_subset {A : Set ℕ} {h n : ℕ} (hs : CollisionRep A h 0 n) :
    Rep A h n := by
  obtain ⟨s, hA, hc, hd, he⟩ := hs
  have hnodup : s.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp
    (le_antisymm s.toFinset_card_le (by simpa using hd))
  refine ⟨⟨s, hnodup⟩, hA, hc, ?_⟩
  change (s.map id).sum = n
  simpa using he

/-- A uniform elementary denominator for the restricted sums of a basis of order h. -/
def collisionDenominator (h : ℕ) : ℕ := 2 * (1 + h * (h+1))^h

/-- The integer threshold may depend on the basis. The denominator depends only on h. -/
theorem collision_density_bound (A : Set ℕ) (h : ℕ) (ha : HasOrder A h) :
    DensityBound (restrictedSums A h) (collisionDenominator h) := by
  classical
  obtain ⟨S, hsA, hfin, hsCard⟩ := (hasOrder_infinite ha).exists_subset_ncard_eq (h+1)
  let T := hfin.toFinset
  have htCard : T.card = h+1 := by simpa only [T, ← Set.ncard_eq_toFinset_card S hfin] using hsCard
  have htA (a : ℕ) (haT : a ∈ T) : a ∈ A := hsA (hfin.mem_toFinset.mp haT)
  let U := T.sup id
  have htU (a : ℕ) (haT : a ∈ T) : a ≤ U := Finset.le_sup (f := id) haT
  obtain ⟨L, hL⟩ := eventually_atTop.mp ha
  refine ⟨2*(h*U+L), ?_⟩
  intro M hM
  let N := M - h*U
  have hNM : N + h*U = M := by dsimp [N]; omega
  have ordinary : Finset.Ico L N ⊆ collisionWindow A h h N := by
    intro n hn
    obtain ⟨hl, hr⟩ := Finset.mem_Ico.mp hn
    obtain ⟨s, hs, hlen, hsum⟩ := hL n hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, s, hs, hlen, by omega, hsum⟩
  have distinct : collisionWindow A h 0 M ⊆ (Finset.range M).filter (· ∈ restrictedSums A h) := by
    intro n hn
    have hx := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hx.1, collision_zero_subset hx.2⟩
  have hcount := collisionWindow_iterate A h h N U T (by omega) htA htU
  rw [htCard, hNM] at hcount
  have hprefix := Finset.card_le_card ordinary
  rw [Nat.card_Ico] at hprefix
  calc
    M ≤ 2*(N-L) := by omega
    _ ≤ 2*(collisionWindow A h h N).card := Nat.mul_le_mul_left 2 hprefix
    _ ≤ 2*((1+h*(h+1))^h * (collisionWindow A h 0 M).card) := Nat.mul_le_mul_left 2 hcount
    _ = collisionDenominator h * (collisionWindow A h 0 M).card := by
      rw [collisionDenominator, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card distinct)

/-- Unconditional density input for the project bridge. -/
theorem uniformDensityInput : UniformDensityInput := by
  intro h _
  exact ⟨collisionDenominator h, by unfold collisionDenominator; positivity, fun A => collision_density_bound A h⟩

#print axioms collision_density_bound
#print axioms uniformDensityInput

end Erdos338.Bridge
