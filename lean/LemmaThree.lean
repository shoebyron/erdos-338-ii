import UniformProgression

/-!
# Counting disjoint witness pairs for restricted sums

Chen–Yang–Zhao, Lemma 3 (https://arxiv.org/html/2611.33191v1).
For the full result use `lemma_three` with specified witnesses, or
`lemma_three_chosen` to choose them from the definition of `restrictedSums`.
The estimates are pointwise in N and r. In Lemma 4 the least qualifying rank may
vary with N: sum over all ranks before taking the lower limit.
-/

namespace Erdos338.Bridge.LemmaThree

open scoped BigOperators Classical

def goodPairs (X : Finset ℕ) (w : ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ X).filter (fun z => Disjoint (w z.1) (w z.2))

def pairFiber (X : Finset ℕ) (w : ℕ → Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (goodPairs X w).filter (fun z => z.1 + z.2 = n)

def pairCount (X : Finset ℕ) (w : ℕ → Finset ℕ) (n : ℕ) : ℕ :=
  (pairFiber X w n).card

/-- Restricted sums in a window. Both endpoints are included. -/
noncomputable def window (A : Set ℕ) (r lo N : ℕ) : Finset ℕ :=
  (Finset.Icc lo N).filter (· ∈ restrictedSums A r)

/-- One choice of witness per value; the counting theorem also accepts any other choice. -/
noncomputable def chosenWitness (A : Set ℕ) (r : ℕ) (x : ℕ) : Finset ℕ :=
  if hx : Rep A r x then hx.choose else ∅

theorem chosenWitness_spec {A : Set ℕ} {r lo N x : ℕ} (hx : x ∈ window A r lo N) :
    (∀ a ∈ chosenWitness A r x, a ∈ A) ∧
    (chosenWitness A r x).card ≤ r ∧ (chosenWitness A r x).sum id = x := by
  have hre : Rep A r x := (Finset.mem_filter.mp hx).2
  simpa only [chosenWitness, dite_eq_left hre] using hre.choose_spec

/-- Equation (1). Removing a fixed summand injects its column into the previous
rank. The sum identity also ensures natural subtraction loses no information. -/
theorem column_bound (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x) (a : ℕ) :
    ((window A r 1 N).filter (fun x => a ∈ w x)).card ≤ (window A (r - 1) 0 N).card := by
  classical
  have removed (x : ℕ) (hx : x ∈ window A r 1 N) (ha : a ∈ w x) :
      ((w x).erase a).sum id + a = x :=
    ((w x).sum_erase_add id ha).trans (hw x hx).2.2
  apply Finset.card_le_card_of_injOn (fun x : ℕ => x - a)
  · intro x hx
    obtain ⟨hxX, ha⟩ := Finset.mem_filter.mp hx
    have hxN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxX).1).2
    have he := removed x hxX ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.sub_le _ _).trans hxN⟩, (w x).erase a, ?_, ?_, ?_⟩
    · intro z hz
      exact (hw x hxX).1 z (Finset.mem_of_mem_erase hz)
    · rw [Finset.card_erase_of_mem ha]
      exact Nat.sub_le_sub_right (hw x hxX).2.1 1
    · change ((w x).erase a).sum id = x - a
      omega
  · intro x hx y hy he
    obtain ⟨hxX, hax⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyX, hay⟩ := Finset.mem_filter.mp hy
    have := removed x hxX hax
    have := removed y hyX hay
    change x - a = y - a at he
    omega

/-- Sum the column bound over the forbidden set, using the project's finite counting lemma. -/
theorem witness_hit_bound (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x) (W : Finset ℕ) :
    ((window A r 1 N).filter (fun y => ¬ Disjoint (w y) W)).card ≤
      W.card * (window A (r - 1) 0 N).card := by
  classical
  refine (Finset.card_le_card ?_).trans (Erdos338.FiniteModular.hit_card
    (window A r 1 N) w W _ (fun a _ => column_bound A r N w hw a))
  intro x hx
  obtain ⟨hxX, hhit⟩ := Finset.mem_filter.mp hx
  obtain ⟨a, hax, haW⟩ := Finset.not_disjoint_iff.mp hhit
  exact Finset.mem_biUnion.mpr ⟨a, haW, Finset.mem_filter.mpr ⟨hxX, hax⟩⟩

/-- Count the same admissible ordered pairs by row and by sum, then project
a fixed-sum fiber to its first coordinate. -/
theorem mass_and_fiber (X : Finset ℕ) (w : ℕ → Finset ℕ) (r e N : ℕ)
    (hsize : ∀ x ∈ X, (w x).card ≤ r) (hN : ∀ x ∈ X, x ≤ N)
    (hhit : ∀ W : Finset ℕ,
      (X.filter (fun y => ¬ Disjoint (w y) W)).card ≤ W.card * e) :
    X.card ^ 2 ≤ (∑ n ∈ Finset.range (2 * N + 1), pairCount X w n) + r * X.card * e ∧
      ∀ n, pairCount X w n ≤ X.card := by
  classical
  let row (x : ℕ) := X.filter (fun y => Disjoint (w y) (w x))
  have rows (x : ℕ) (hx : x ∈ X) : X.card ≤ (row x).card + r * e := by
    have hpart := Finset.card_filter_add_card_filter_not (s := X)
      (fun y => Disjoint (w y) (w x))
    have hbad := (hhit (w x)).trans (Nat.mul_le_mul_right e (hsize x hx))
    change X.card ≤ (X.filter (fun y => Disjoint (w y) (w x))).card + r * e
    omega
  have hmem (z : ℕ × ℕ) : z ∈ goodPairs X w ↔ z.1 ∈ X ∧ z.2 ∈ row z.1 := by
    simp only [goodPairs, row, Finset.mem_filter, Finset.mem_product, and_assoc]
    rw [disjoint_comm (a := w z.1)]
  have byRow : (goodPairs X w).card = ∑ x ∈ X, (row x).card := by
    simpa using (Finset.sum_finset_product (goodPairs X w) X row hmem
      (f := fun _ => (1 : ℕ)))
  have bySum : (goodPairs X w).card = ∑ n ∈ Finset.range (2 * N + 1), pairCount X w n := by
    apply Finset.card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.1 + z.2)
    intro z hz
    have hz' := (hmem z).mp hz
    have hx := hN z.1 hz'.1
    have hy := hN z.2 (Finset.mem_filter.mp hz'.2).1
    apply Finset.mem_range.mpr
    change z.1 + z.2 < 2 * N + 1
    omega
  constructor
  · calc
      X.card ^ 2 = ∑ _x ∈ X, X.card := by simp [pow_two]
      _ ≤ ∑ x ∈ X, ((row x).card + r * e) := Finset.sum_le_sum rows
      _ = _ := by rw [Finset.sum_add_distrib, ← byRow, bySum]; simp [mul_comm, mul_left_comm]
  · intro n
    apply Finset.card_le_card_of_injOn (s := pairFiber X w n) (t := X) Prod.fst
    · intro z hz
      exact ((hmem z).mp (Finset.mem_filter.mp hz).1).1
    · intro a ha b hb he
      have ha' : a.1 + a.2 = n := (Finset.mem_filter.mp ha).2
      have hb' : b.1 + b.2 = n := (Finset.mem_filter.mp hb).2
      exact Prod.ext he (by change a.1 = b.1 at he; omega)

/-- At fixed sum, either coordinate determines the pair. Thus the pairs whose
two witnesses together hit a forbidden set occupy at most two copies of the
individual witness hit count. -/
theorem fiber_hit_bound (X : Finset ℕ) (w : ℕ → Finset ℕ) (e n : ℕ)
    (hhit : ∀ W : Finset ℕ, (X.filter (fun y => ¬ Disjoint (w y) W)).card ≤ W.card * e)
    (W : Finset ℕ) :
    ((pairFiber X w n).filter (fun z => ¬ Disjoint (w z.1 ∪ w z.2) W)).card ≤
      2 * W.card * e := by
  classical
  let P := pairFiber X w n
  let H := X.filter (fun y => ¬ Disjoint (w y) W)
  have facts (z : ℕ × ℕ) (hz : z ∈ P) : z.1 ∈ X ∧ z.2 ∈ X ∧ z.1 + z.2 = n := by
    have h := Finset.mem_filter.mp hz
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp h.1).1
    exact ⟨hm.1, hm.2, h.2⟩
  have project (f : ℕ × ℕ → ℕ) (inj : Set.InjOn f (P : Set (ℕ × ℕ)))
      (hX : ∀ z ∈ P, f z ∈ X) :
      (P.filter (fun z => ¬ Disjoint (w (f z)) W)).card ≤ H.card := by
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      obtain ⟨hzP, hw⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hX z hzP, hw⟩
    · intro z hz z' hz' he
      exact inj (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz').1 he
  let L := P.filter (fun z => ¬ Disjoint (w z.1) W)
  let R := P.filter (fun z => ¬ Disjoint (w z.2) W)
  have hl : L.card ≤ H.card := by
    apply project Prod.fst _ (fun z hz => (facts z hz).1)
    intro z hz y hy he
    have h₁ := (facts z hz).2.2
    have h₂ := (facts y hy).2.2
    exact Prod.ext he (by omega)
  have hr : R.card ≤ H.card := by
    apply project Prod.snd _ (fun z hz => (facts z hz).2.1)
    intro z hz y hy he
    have h₁ := (facts z hz).2.2
    have h₂ := (facts y hy).2.2
    exact Prod.ext (by omega) he
  have hsub : P.filter (fun z => ¬ Disjoint (w z.1 ∪ w z.2) W) ⊆ L ∪ R := by
    intro z hz
    obtain ⟨hp, hw⟩ := Finset.mem_filter.mp hz
    by_cases hd : Disjoint (w z.1) W
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hp, fun he => hw (Finset.disjoint_union_left.mpr ⟨hd, he⟩)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hd⟩)
  calc
    _ ≤ (L ∪ R).card := Finset.card_le_card hsub
    _ ≤ L.card + R.card := Finset.card_union_le _ _
    _ ≤ W.card * e + W.card * e := Nat.add_le_add (hl.trans (hhit W)) (hr.trans (hhit W))
    _ = 2 * W.card * e := by ring

/-- Greedily pack pairs without reusing any element of a chosen witness. -/
theorem pack_pairs (P : Finset (ℕ × ℕ)) (U : ℕ × ℕ → Finset ℕ) (r e Q : ℕ)
    (hsize : ∀ z ∈ P, (U z).card ≤ 2 * r)
    (hhit : ∀ W : Finset ℕ, (P.filter (fun z => ¬ Disjoint (U z) W)).card ≤ 2 * W.card * e)
    (hcount : 4 * r * (Q - 1) * e < P.card) :
    ∃ f : Fin Q → ℕ × ℕ, (∀ i, f i ∈ P) ∧ Pairwise (fun i j => Disjoint (U (f i)) (U (f j))) := by
  classical
  suffices aux : ∀ k ≤ Q, ∃ f : Fin k → ℕ × ℕ, (∀ i, f i ∈ P) ∧
      Pairwise (fun i j => Disjoint (U (f i)) (U (f j))) from aux Q le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun i => i.elim0, by intro i; exact i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨f, hf, hdis⟩ := ih (by omega)
    let W := Finset.univ.biUnion (fun i => U (f i))
    have hW : W.card ≤ k * (2 * r) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_biUnion_le_card_mul Finset.univ (fun i => U (f i)) (2 * r)
          (fun i _ => hsize _ (hf i))
    have hroom : 2 * W.card * e ≤ 4 * r * (Q - 1) * e := calc
      2 * W.card * e ≤ 2 * (k * (2 * r)) * e := by gcongr
      _ = 4 * r * k * e := by ring
      _ ≤ 4 * r * (Q - 1) * e := by gcongr; omega
    obtain ⟨z, hz, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (lt_of_le_of_lt ((hhit W).trans hroom) hcount)
    have hzW : Disjoint (U z) W := by
      by_contra hn
      exact hout (Finset.mem_filter.mpr ⟨hz, hn⟩)
    have hzdis (i : Fin k) : Disjoint (U z) (U (f i)) :=
      hzW.mono_right (fun x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)
    refine ⟨Fin.cons z f, ?_, ?_⟩
    · exact Fin.forall_fin_succ.mpr ⟨by simpa using hz, by simpa using hf⟩
    · rw [pairwise_fin_succ_iff]
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        (show (∀ i, Disjoint (U (f i)) (U z)) ∧ (∀ i, Disjoint (U z) (U (f i))) ∧
          Pairwise (fun i j => Disjoint (U (f i)) (U (f j))) from
          ⟨fun i => (hzdis i).symm, hzdis, hdis⟩)

/-- A positive member of the existing rich-sum set is exactly a sum with
the specified number of pairwise disjoint, nonempty witnesses. -/
theorem mem_richSums_iff_nonempty {A : Set ℕ} {s q n : ℕ} (hn : 0 < n) :
    n ∈ richSums A s q ↔ ∃ G : Fin q → Finset ℕ,
      (∀ i, (G i).Nonempty ∧ (∀ a ∈ G i, a ∈ A) ∧ (G i).card ≤ s ∧ (G i).sum id = n) ∧
      Pairwise (fun i j => Disjoint (G i) (G j)) := by
  constructor
  · rintro (he | ⟨G, hw, hp⟩)
    · omega
    · refine ⟨G, fun i => ⟨?_, hw i⟩, hp⟩
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have hsum := (hw i).2.2
      rw [he, Finset.sum_empty] at hsum
      omega
  · rintro ⟨G, hG, hp⟩
    exact Or.inr ⟨G, fun i => (hG i).2, hp⟩

/-- The three conclusions for a single choice of witnesses. The fiber is over
ordered pairs, and the sum over `range (2 * N + 1)` includes both endpoints. -/
def Estimates (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ) : Prop :=
  let X := window A r 1 N
  let M := X.card
  let e := (window A (r - 1) 0 N).card
  let p := pairCount X w
  M ^ 2 ≤ (∑ n ∈ Finset.range (2 * N + 1), p n) + r * M * e ∧
    (∀ n, p n ≤ M) ∧
    ∀ Q n, 4 * r * (Q - 1) * e < p n → 0 < n ∧ n ∈ richSums A (2 * r) Q

/-- Chen–Yang–Zhao, Lemma 3. This holds for every valid choice of one
restricted witness per value, with no conditions relating different windows. -/
theorem lemma_three (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x) :
    Estimates A r N w := by
  classical
  let X := window A r 1 N
  let e := (window A (r - 1) 0 N).card
  have hxI {x : ℕ} (hx : x ∈ X) : 1 ≤ x ∧ x ≤ N :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
  have hhit := witness_hit_bound A r N w hw
  obtain ⟨hmass, hcap⟩ := mass_and_fiber X w r e N
    (fun x hx => (hw x hx).2.1) (fun _ hx => (hxI hx).2) hhit
  refine ⟨hmass, hcap, ?_⟩
  intro Q n hpop
  let P := pairFiber X w n
  let U (z : ℕ × ℕ) := w z.1 ∪ w z.2
  have facts {z : ℕ × ℕ} (hz : z ∈ P) :
      z.1 ∈ X ∧ z.2 ∈ X ∧ Disjoint (w z.1) (w z.2) ∧ z.1 + z.2 = n := by
    obtain ⟨hgood, hsum⟩ := Finset.mem_filter.mp hz
    obtain ⟨hprod, hd⟩ := Finset.mem_filter.mp hgood
    exact ⟨(Finset.mem_product.mp hprod).1, (Finset.mem_product.mp hprod).2, hd, hsum⟩
  have sizes : ∀ z ∈ P, (U z).card ≤ 2 * r := by
    intro z hz
    obtain ⟨hx, hy, _, _⟩ := facts hz
    have hcards := Nat.add_le_add (hw _ hx).2.1 (hw _ hy).2.1
    exact (Finset.card_union_le _ _).trans (by simpa only [two_mul] using hcards)
  have hP : 4 * r * (Q - 1) * e < P.card := hpop
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hP)
  obtain ⟨hx, _, _, hzn⟩ := facts hz
  have xpos := (hxI hx).1
  have hn : 0 < n := by omega
  obtain ⟨f, hf, hdis⟩ := pack_pairs P U r e Q sizes (fiber_hit_bound X w e n hhit) hP
  refine ⟨hn, Or.inr ⟨fun i => U (f i), ?_, hdis⟩⟩
  intro i
  obtain ⟨hx, hy, hd, hsum⟩ := facts (hf i)
  refine ⟨?_, sizes _ (hf i), ?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · exact (hw _ hx).1 a h
    · exact (hw _ hy).1 a h
  · change (w (f i).1 ∪ w (f i).2).sum id = n
    rw [Finset.sum_union hd, (hw _ hx).2.2, (hw _ hy).2.2, hsum]

/-- Specialization with witnesses chosen directly from the definition of restricted sums. -/
theorem lemma_three_chosen (A : Set ℕ) (r N : ℕ) :
    Estimates A r N (chosenWitness A r) :=
  lemma_three A r N (chosenWitness A r) (fun _ hx => chosenWitness_spec hx)

/-- The threshold conclusion with the actual nonempty representation family exposed. -/
theorem popular_disjoint_representations (A : Set ℕ) (r N Q n : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x)
    (hpop : 4 * r * (Q - 1) * (window A (r - 1) 0 N).card < pairCount (window A r 1 N) w n) :
    ∃ G : Fin Q → Finset ℕ,
      (∀ i, (G i).Nonempty ∧ (∀ a ∈ G i, a ∈ A) ∧ (G i).card ≤ 2 * r ∧ (G i).sum id = n) ∧
      Pairwise (fun i j => Disjoint (G i) (G j)) := by
  obtain ⟨hn, hrich⟩ := (lemma_three A r N w hw).2.2 Q n hpop
  exact (mem_richSums_iff_nonempty hn).mp hrich

#print axioms lemma_three
#print axioms popular_disjoint_representations
#print axioms lemma_three_chosen
#print axioms mem_richSums_iff_nonempty

end Erdos338.Bridge.LemmaThree
