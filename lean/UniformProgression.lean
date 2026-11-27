import BoundedByOrderFixed

/-! Uniform constants and the deletion step of Chen–Yang–Zhao, Lemma 4.
Source: https://arxiv.org/html/2611.33191v1#S2
-/

namespace Erdos338.Bridge

/-- The denominator of the current density and the cost of all earlier stages.
At stage `t`, the paper's index is `r = h - t`. -/
structure ProgressionStage where
  denominator : ℕ
  cost : ℕ

def ProgressionStage.length (s : ProgressionStage) : ℕ :=
  8 * s.denominator ^ 2

def ProgressionStage.multiplicity (s : ProgressionStage) (r b : ℕ) : ℕ :=
  b + s.cost + 2 * r * (s.length - 1) + 1

def progressionStage (h m b : ℕ) : ℕ → ProgressionStage
  | 0 => ⟨2 * m, 0⟩
  | t + 1 =>
    let s := progressionStage h m b t
    let r := h - t
    ⟨s.denominator ^ 2 * (64 * r * s.multiplicity r b),
      s.cost + 2 * r * s.length⟩

noncomputable def progressionAlpha (h m b t : ℕ) : ℝ :=
  1 / ((progressionStage h m b t).denominator : ℝ)

def progressionL (h m b t : ℕ) : ℕ := (progressionStage h m b t).length

def progressionQ (h m b t : ℕ) : ℕ := (progressionStage h m b t).multiplicity (h - t) b

def progressionK (h m b : ℕ) : ℕ := (progressionStage h m b h).cost

theorem progressionCost_eq_sum (h m b t : ℕ) :
    (progressionStage h m b t).cost = ∑ j ∈ Finset.range t, 2 * (h - j) * progressionL h m b j := by
  induction t with
  | zero => simp [progressionStage]
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; rfl

theorem progressionK_eq_sum (h m b : ℕ) :
    progressionK h m b = ∑ t ∈ Finset.range h, 2 * (h - t) * progressionL h m b t :=
  progressionCost_eq_sum h m b h

theorem progressionK_pos (h m b : ℕ) (hh : 0 < h) (hm : 0 < m) :
    0 < progressionK h m b := by
  rw [progressionK_eq_sum]
  have bound := Finset.single_le_sum (f := fun j => 2 * (h - j) * progressionL h m b j)
    (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr hh)
  have hL : 0 < progressionL h m b 0 := by
    change 0 < 8 * (2 * m) ^ 2
    positivity
  exact lt_of_lt_of_le (by simpa only [Nat.sub_zero] using
    (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hh) hL)) bound

theorem progressionQ_eq (h m b t : ℕ) :
    progressionQ h m b t = b + (∑ j ∈ Finset.range t, 2 * (h - j) * progressionL h m b j)
      + 2 * (h - t) * (progressionL h m b t - 1) + 1 := by
  rw [← progressionCost_eq_sum]
  rfl

theorem progressionDenominator_pos (h m b t : ℕ) (hm : 0 < m) (ht : t ≤ h) :
    0 < (progressionStage h m b t).denominator := by
  induction t with
  | zero => change 0 < 2 * m; positivity
  | succ t ih =>
    have hd := ih (by omega)
    have hr : 0 < h - t := by omega
    have hq : 0 < (progressionStage h m b t).multiplicity (h - t) b := Nat.zero_lt_succ _
    change 0 < (progressionStage h m b t).denominator ^ 2 *
      (64 * (h - t) * (progressionStage h m b t).multiplicity (h - t) b)
    positivity

theorem progressionAlpha_zero (h m b : ℕ) :
    progressionAlpha h m b 0 = 1 / (2 * (m : ℝ)) := by
  simp [progressionAlpha, progressionStage]

/-- Equation (2) with the initial density `1/(2m)`, read in descending order of rank. -/
theorem progression_equation_two (h m b t : ℕ) (hm : 0 < m) (ht : t < h) :
    0 < progressionAlpha h m b t ∧
    progressionL h m b t = ⌈8 / progressionAlpha h m b t ^ 2⌉₊ ∧
    progressionQ h m b t =
      b + (∑ j ∈ Finset.range t, 2 * (h - j) * progressionL h m b j)
        + 2 * (h - t) * (progressionL h m b t - 1) + 1 ∧
    progressionAlpha h m b (t + 1) =
      progressionAlpha h m b t ^ 2 / (64 * ((h - t : ℕ) : ℝ) * progressionQ h m b t) := by
  have hd := progressionDenominator_pos h m b t hm ht.le
  refine ⟨by unfold progressionAlpha; positivity, ?_, progressionQ_eq h m b t, ?_⟩
  · have he : 8 / progressionAlpha h m b t ^ 2 = ((progressionL h m b t : ℕ) : ℝ) := by
      simp [progressionAlpha, progressionL, ProgressionStage.length]
    rw [he, Nat.ceil_natCast]
  · simp [progressionAlpha, progressionStage, progressionQ, div_eq_mul_inv,
      mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

end Erdos338.Bridge


namespace Erdos338.Bridge

open Filter
open scoped Classical

/-- The lower density using the paper's interval of positive indices. -/
noncomputable def positiveLowerDensity (B : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (((Finset.Icc 1 N).filter (· ∈ B)).card : ℝ) / N) atTop

/-- The integer counting hypothesis supplies a strict, set-independent starting density. -/
theorem half_inv_lt_positiveLowerDensity {B : Set ℕ} {m : ℕ}
    (hm : 0 < m) (hB : DensityBound B m) :
    1 / (2 * (m : ℝ)) < positiveLowerDensity B := by
  classical
  obtain ⟨N₀, hN₀⟩ := hB
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hgap : 1 / (2 * (m : ℝ)) < 2 / (3 * (m : ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  apply hgap.trans_le
  unfold positiveLowerDensity
  refine le_liminf_of_le (f := (atTop : Filter ℕ)) ?_ ?_
  · apply isCoboundedUnder_ge_of_le (atTop : Filter ℕ) (x := (1 : ℝ))
    intro N
    by_cases hN : N = 0
    · simp [hN]
    · have hpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      apply (div_le_iff₀ hpos).2
      rw [one_mul]
      have hcard : ((Finset.Icc 1 N).filter (· ∈ B)).card ≤ N := by
        simpa using (Finset.card_filter_le (Finset.Icc 1 N) (fun x => x ∈ B))
      exact_mod_cast hcard
  · filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (3 * m)] with N hN hlarge
    let C := ((Finset.Icc 1 N).filter (· ∈ B)).card
    have hsub : (Finset.range N).filter (· ∈ B) ⊆
        insert 0 ((Finset.Icc 1 N).filter (· ∈ B)) := by
      intro x hx
      obtain ⟨hxN, hxB⟩ := Finset.mem_filter.mp hx
      have hxlt := Finset.mem_range.mp hxN
      by_cases hx : x = 0
      · simp [hx]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hxB⟩)
    have hc : ((Finset.range N).filter (· ∈ B)).card ≤ C + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hb := (hN₀ N hN).trans (Nat.mul_le_mul_left m hc)
    rw [Nat.mul_add, Nat.mul_one] at hb
    have hn : 2 * N ≤ (3 * m) * C := by
      rw [Nat.mul_assoc]
      omega
    have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    apply (div_le_div_iff₀ (by positivity) hpos).2
    change 2 * (N : ℝ) ≤ (C : ℝ) * (3 * (m : ℝ))
    rw [mul_comm (C : ℝ)]
    exact_mod_cast hn

end Erdos338.Bridge


namespace Erdos338.Bridge

/-- The numerical step after Lemma 3: its lower and upper pair counts force
enough popular sums to contribute at least `6 * N` at the chosen rank. -/
theorem progression_many_popular_sums
    (N r Q α L M e D : ℝ) (hN : 0 < N) (hr : 0 < r) (hQ : 0 < Q)
    (hα : 0 < α) (he : 0 ≤ e) (hM : α * N ≤ M) (hMN : M ≤ N)
    (hsmall : e ≤ 2 * (α ^ 2 / (64 * r * Q)) * N)
    (hcounts : M ^ 2 - r * M * e ≤ N * D + 8 * r * (Q - 1) * e * N)
    (hL : 8 / α ^ 2 ≤ L) :
    (3 / 4 : ℝ) * α ^ 2 * N ≤ D ∧ 6 * N ≤ L * D := by
  have hαN : 0 ≤ α * N := (mul_pos hα hN).le
  have hsq := mul_self_le_mul_self hαN hM
  have hden : 0 < 64 * r * Q := by positivity
  have hsmall' : e ≤ (2 * α ^ 2 * N) / (64 * r * Q) := by
    calc
      e ≤ _ := hsmall
      _ = _ := by ring
  have heN := mul_le_mul_of_nonneg_right ((le_div_iff₀ hden).mp hsmall') hN.le
  have hre : 0 ≤ r * e := mul_nonneg hr.le he
  have herr := mul_le_mul_of_nonneg_right hMN hre
  have hD : (3 / 4 : ℝ) * α ^ 2 * N ≤ D := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hsq, heN, herr, hcounts, mul_nonneg hre hN.le]
  have hα2 : 0 < α ^ 2 := by positivity
  have hscale := (div_le_iff₀ hα2).mp hL
  have hL0 : 0 ≤ L := (by positivity : (0 : ℝ) ≤ 8 / α ^ 2).trans hL
  refine ⟨hD, ?_⟩
  have hprod := mul_le_mul_of_nonneg_left hD hL0
  have hbound := mul_le_mul_of_nonneg_right hscale hN.le
  nlinarith only [hprod, hbound]

end Erdos338.Bridge


open Filter
namespace Erdos338.Bridge
/-- An infinite, eventually periodic set contains a full tail of a residue class
with the same modulus (Chen–Yang–Zhao, Lemma 4, equation (3)). -/
theorem progression_of_eventual_periodicity
    {S : Set ℕ} (hinf : S.Infinite) {g : ℕ} {T : Set (ZMod g)}
    (hperiod : ∀ᶠ n : ℕ in atTop, n ∈ S ↔ (n : ZMod g) ∈ T) :
    ∃ a : ZMod g, ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ n ≥ N₀, (n : ZMod g) = a → n ∈ S := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hperiod
  obtain ⟨u, hu, hNu⟩ := hinf.exists_gt N
  have hmem : (u : ZMod g) ∈ T := (hN u hNu.le).mp hu
  refine ⟨(u : ZMod g), N + 1, Nat.succ_pos _, ?_⟩
  intro n hn hcong
  exact (hN n (by omega)).mpr (hcong ▸ hmem)

/-- The paper defines eventual periodicity using finite differences in both
directions between a set and the union of residue classes. -/
theorem progression_of_finite_differences
    {S : Set ℕ} (hinf : S.Infinite) {g : ℕ} {T : Set (ZMod g)}
    (hextra : (S \ {n : ℕ | (n : ZMod g) ∈ T}).Finite)
    (hmissing : ({n : ℕ | (n : ZMod g) ∈ T} \ S).Finite) :
    ∃ a : ZMod g, ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ n ≥ N₀, (n : ZMod g) = a → n ∈ S := by
  apply progression_of_eventual_periodicity (T := T) hinf
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hextra.eventually_cofinite_notMem, hmissing.eventually_cofinite_notMem]
    with n he hm
  change ¬ (n ∈ S ∧ (n : ZMod g) ∉ T) at he
  change ¬ ((n : ZMod g) ∈ T ∧ n ∉ S) at hm
  tauto
end Erdos338.Bridge


/-! The sets used in equations (3)–(5) of Chen–Yang–Zhao, Lemma 4.
The value zero allows unused slots, including all slots at any omitted level. -/
namespace Erdos338.Bridge

/-- The paper's set of positive sums with many disjoint witnesses, with zero adjoined. -/
def richSums (A : Set ℕ) (w q : ℕ) : Set ℕ :=
  {d | d = 0 ∨ ∃ G : Fin q → Finset ℕ,
    (∀ i, (∀ x ∈ G i, x ∈ A) ∧ (G i).card ≤ w ∧ (G i).sum id = d) ∧
      Pairwise (fun i j => Disjoint (G i) (G j))}

private theorem chooseOutside {A : Set ℕ} {w q d : ℕ} (hd : d ∈ richSums A w q)
    (W : Finset ℕ) (hq : W.card < q) :
    ∃ G : Finset ℕ, (∀ x ∈ G, x ∈ A) ∧ G.card ≤ w ∧ G.sum id = d ∧ Disjoint G W := by
  classical
  rcases hd with rfl | ⟨G, hG, hpair⟩
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  have hex : ∃ i, Disjoint (G i) W := by
    by_contra! hn
    have hh (i : Fin q) : ∃ x, x ∈ G i ∧ x ∈ W := Finset.not_disjoint_iff.mp (hn i)
    choose x hx hw using hh
    let f (i : Fin q) : ↥W := ⟨x i, hw i⟩
    have hinj : Function.Injective f := by
      intro i j he
      by_contra hne
      have e : x i = x j := congrArg Subtype.val he
      exact (Finset.disjoint_left.mp (hpair hne)) (hx i) (e ▸ hx j)
    have := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨G i, (hG i).1, (hG i).2.1, (hG i).2.2, hi⟩

/-- Add exactly `k` terms of `C` to one element of `B`, allowing repeated values. -/
def addCopies (B C : Set ℕ) : ℕ → Set ℕ
  | 0 => B
  | k + 1 => {n | ∃ x ∈ addCopies B C k, ∃ d ∈ C, x + d = n}

private theorem rep_addCopies {A B : Set ℕ} {F : Finset ℕ} {p w q L : ℕ}
    (base : ∀ x ∈ B, Rep (A \ (F : Set ℕ)) p x)
    (room : F.card + p + w * (L - 1) < q) (k : ℕ) (hk : k ≤ L) :
    ∀ n ∈ addCopies B (richSums A w q) k, Rep (A \ (F : Set ℕ)) (p + w * k) n := by
  classical
  induction k with
  | zero => simpa [addCopies] using base
  | succ k ih =>
    rintro n ⟨x, hx, d, hd, rfl⟩
    obtain ⟨T, hT, ht, hsum⟩ := ih (by omega) x hx
    have hle : w * k ≤ w * (L - 1) := Nat.mul_le_mul_left w (by omega)
    have hroom : (F ∪ T).card < q := by
      have := Finset.card_union_le F T
      omega
    obtain ⟨G, hG, hg, hdsum, hdis⟩ := chooseOutside hd (F ∪ T) hroom
    have hGT : Disjoint G T := Finset.disjoint_left.mpr fun _ hx ht' =>
      Finset.disjoint_left.mp hdis hx (Finset.mem_union_right _ ht')
    refine ⟨T ∪ G, ?_, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with hat | hag
      · exact hT a hat
      · exact ⟨hG a hag, fun haf => Finset.disjoint_left.mp hdis hag (Finset.mem_union_left _ haf)⟩
    · rw [Nat.mul_succ]
      have := Finset.card_union_le T G
      omega
    · rw [Finset.sum_union hGT.symm, hsum, hdsum]

/-- Start with the empty sum and add the paper's levels in descending rank.
Using all levels enlarges its sumset in (3), since every level contains zero. -/
def progressionSums (A : Set ℕ) (h m b : ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | t + 1 => addCopies (progressionSums A h m b t)
      (richSums A (2 * (h - t)) (progressionQ h m b t)) (progressionL h m b t)

/-- Greedy disjoint representatives, equations (4) and (5), at any prefix of the levels. -/
theorem rep_progressionSums {A : Set ℕ} {h m b : ℕ} (F : Finset ℕ) (hf : F.card ≤ b)
    (t : ℕ) : ∀ n ∈ progressionSums A h m b t,
      Rep (A \ (F : Set ℕ)) (progressionStage h m b t).cost n := by
  induction t with
  | zero =>
    intro n hn
    have he : n = 0 := hn
    exact ⟨∅, by simp, by simp, by simp [he]⟩
  | succ t ih =>
    apply rep_addCopies ih _ _ (le_refl _)
    change F.card + _ + _ < b + (progressionStage h m b t).cost +
      2 * (h - t) * (progressionL h m b t - 1) + 1
    omega

/-- Equation (3) for the fixed sumset suffices for the full progression input.
Its modulus, class and threshold are all chosen before the deletion. -/
theorem uniformProgressionInput_of_sumset_progression
    (tail : ∀ h m b : ℕ, 0 < h → 0 < m →
      ∀ A : Set ℕ, DensityBound (restrictedSums A h) m →
        ∃ g : ℕ, 0 < g ∧ ∃ a : ZMod g, ∃ N₀ : ℕ,
          ∀ n : ℕ, N₀ ≤ n → (n : ZMod g) = a → n ∈ progressionSums A h m b h) :
    UniformProgressionInput := by
  intro h m b hh hm
  refine ⟨progressionK h m b, ?_⟩
  intro A hA
  obtain ⟨g, hg, a, N₀, hn⟩ := tail h m b hh hm A hA
  exact ⟨g, hg, a, N₀, fun F _ hF n hN ha =>
    rep_progressionSums F hF h n (hn n hN ha)⟩

private theorem subset_addCopies {B B' C : Set ℕ} (sub : B ⊆ B') (k : ℕ) :
    addCopies B C k ⊆ addCopies B' C k := by
  induction k with
  | zero => exact sub
  | succ k ih =>
    rintro n ⟨x, hx, d, hd, rfl⟩
    exact ⟨x, ih hx, d, hd, rfl⟩

private theorem subset_addCopies_of_zero {B C : Set ℕ} (hz : 0 ∈ C) (k : ℕ) :
    B ⊆ addCopies B C k := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
    intro x hx
    exact ⟨x, ih hx, 0, hz, Nat.add_zero x⟩

open scoped Classical in
/-- The paper's sumset S from just the infinite levels (following equation (2)). -/
noncomputable def infiniteLevelSums (A : Set ℕ) (h m b : ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | t + 1 =>
    let C := richSums A (2 * (h - t)) (progressionQ h m b t)
    let B := infiniteLevelSums A h m b t
    if C.Infinite then addCopies B C (progressionL h m b t) else B

theorem infiniteLevelSums_subset (A : Set ℕ) (h m b t : ℕ) :
    infiniteLevelSums A h m b t ⊆ progressionSums A h m b t := by
  classical
  induction t with
  | zero => exact Set.Subset.rfl
  | succ t ih =>
    simp only [infiniteLevelSums, progressionSums]
    split
    · exact subset_addCopies ih _
    · exact ih.trans (subset_addCopies_of_zero (Or.inl rfl) _)

open scoped Classical in
/-- Unbounded weighted counts on finitely many ranks force an infinite rank. -/
theorem infinite_rank_of_counts {C : ℕ → Set ℕ} {L : ℕ → ℕ} {h : ℕ}
    (mass : ∀ᶠ N : ℕ in Filter.atTop,
      ∃ t < h, N ≤ L t * ((Finset.Icc 0 (2*N)).filter (· ∈ C t)).card) :
    ∃ t < h, (C t).Infinite := by
  classical
  by_contra! hfin
  let B := ∑ t ∈ Finset.range h, L t * (C t).ncard
  obtain ⟨N₀, hN⟩ := Filter.eventually_atTop.mp mass
  let N := max N₀ (B + 1)
  obtain ⟨t, ht, hcount⟩ := hN N (le_max_left _ _)
  let P := (Finset.Icc 0 (2*N)).filter (· ∈ C t)
  have hsub : (P : Set ℕ) ⊆ C t := fun x hx => (Finset.mem_filter.mp hx).2
  have hc : P.card ≤ (C t).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (hfin t ht)
  have hbound : L t * (C t).ncard ≤ B :=
    Finset.single_le_sum (f := fun j => L j * (C j).ncard)
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
  have hle : N ≤ B := hcount.trans ((Nat.mul_le_mul_left _ hc).trans hbound)
  have := le_max_right N₀ (B + 1)
  omega

private theorem infiniteLevelSums_mono (A : Set ℕ) (h m b t : ℕ) :
    infiniteLevelSums A h m b t ⊆ infiniteLevelSums A h m b (t+1) := by
  classical
  simp only [infiniteLevelSums]
  split
  · exact subset_addCopies_of_zero (Or.inl rfl) _
  · exact Set.Subset.rfl

private theorem zero_mem_infiniteLevelSums (A : Set ℕ) (h m b t : ℕ) :
    0 ∈ infiniteLevelSums A h m b t := by
  induction t with
  | zero => rfl
  | succ t ih => exact infiniteLevelSums_mono A h m b t ih

theorem infiniteLevelSums_infinite {A : Set ℕ} {h m b u : ℕ}
    (hm : 0 < m) (hu : u < h)
    (hi : (richSums A (2 * (h-u)) (progressionQ h m b u)).Infinite) :
    (infiniteLevelSums A h m b h).Infinite := by
  classical
  have hpos : 0 < progressionL h m b u := by
    have := progressionDenominator_pos h m b u hm hu.le
    unfold progressionL ProgressionStage.length
    positivity
  have hone : (infiniteLevelSums A h m b (u+1)).Infinite := by
    simp only [infiniteLevelSums, hi, ↓reduceIte]
    apply hi.mono
    intro d hd
    cases he : progressionL h m b u with
    | zero => omega
    | succ k =>
      exact ⟨0, subset_addCopies_of_zero (Or.inl rfl) k
        (zero_mem_infiniteLevelSums A h m b u), d, hd, Nat.zero_add d⟩
  have hgrow : Monotone (infiniteLevelSums A h m b) :=
    monotone_nat_of_le_succ (infiniteLevelSums_mono A h m b)
  exact hone.mono (hgrow hu)

/-- The remaining analytic hypothesis concerns a sumset built before any deletion.
Once it holds for all sets above the common density, the same explicit K works for all of them. -/
theorem progressionK_works_of_periodicity (h m b : ℕ) (hm : 0 < m)
    (period : ∀ A : Set ℕ,
      progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h) →
      (infiniteLevelSums A h m b h).Infinite ∧
        ∃ g : ℕ, 0 < g ∧ ∃ T : Set (ZMod g),
          ∀ᶠ n : ℕ in Filter.atTop, n ∈ infiniteLevelSums A h m b h ↔ (n : ZMod g) ∈ T) :
    ∀ A : Set ℕ, DensityBound (restrictedSums A h) m →
      ∃ g : ℕ, 0 < g ∧ ∃ a : ZMod g, ∃ N₀ : ℕ, 0 < N₀ ∧
        ∀ F : Finset ℕ, F.card ≤ b → ∀ n : ℕ, N₀ ≤ n → (n : ZMod g) = a →
          Rep (A \ (F : Set ℕ)) (progressionK h m b) n := by
  intro A hd
  have hα := half_inv_lt_positiveLowerDensity hm hd
  rw [← progressionAlpha_zero h m b] at hα
  obtain ⟨hinf, g, hg, T, hperiod⟩ := period A hα
  obtain ⟨a, N₀, hN₀, hn⟩ := progression_of_eventual_periodicity hinf hperiod
  refine ⟨g, hg, a, N₀, hN₀, ?_⟩
  intro F hF n hN hcong
  exact rep_progressionSums F hF h n (infiniteLevelSums_subset A h m b h (hn n hN hcong))

/-- The reduction specialized to the original target, for all positive h and m. -/
theorem uniformProgressionInput_of_periodicity
    (period : ∀ h m b : ℕ, 0 < h → 0 < m → ∀ A : Set ℕ,
      progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h) →
      (infiniteLevelSums A h m b h).Infinite ∧
        ∃ g : ℕ, 0 < g ∧ ∃ T : Set (ZMod g),
          ∀ᶠ n : ℕ in Filter.atTop, n ∈ infiniteLevelSums A h m b h ↔ (n : ZMod g) ∈ T) :
    UniformProgressionInput := by
  intro h m b hh hm
  refine ⟨progressionK h m b, ?_⟩
  intro A hA
  obtain ⟨g, hg, a, N₀, _, hn⟩ :=
    progressionK_works_of_periodicity h m b hm (period h m b hh hm) A hA
  exact ⟨g, hg, a, N₀, fun F _ hF => hn F hF⟩

#print axioms uniformProgressionInput_of_periodicity
#print axioms progressionK_works_of_periodicity
#print axioms progression_equation_two
#print axioms rep_progressionSums

end Erdos338.Bridge
