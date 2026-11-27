import UniformProgression

/-! Reduction of the project density input to Hegyvári–Hennecart–Plagne's
quantitative lower-density theorem, stated as Theorem 4.8 in Hegyvári's
2017 dissertation, https://real-d.mtak.hu/1038/7/dc_1260_16_doktori_mu.pdf .
The sets in that theorem use exactly h summands from a set of positive
integers. The project allows at most h summands from a subset of ℕ. -/

namespace Erdos338.Bridge

open Filter
open scoped Classical BigOperators

/-- Ordinary sums of exactly h elements, allowing repetitions. -/
def exactOrdinarySums (B : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ s : Multiset ℕ, (∀ x ∈ s, x ∈ B) ∧ s.card = h ∧ s.sum = n}

/-- Sums of exactly h distinct elements. -/
def exactDistinctSums (B : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ B) ∧ s.card = h ∧ s.sum id = n}

/-- The denominator in the published quantitative bound. -/
noncomputable def hhpDenominator (h : ℕ) : ℝ :=
  (h : ℝ) ^ h * Real.exp (Real.pi * Real.sqrt (2 * h / 3 : ℝ))

/-- The lower-density inequality in HHP, stated only for positive ordinary density. -/
def HHPDensityEstimate : Prop :=
  ∀ (h : ℕ), 0 < h → ∀ B : Set ℕ, (∀ x ∈ B, 0 < x) →
    0 < positiveLowerDensity (exactOrdinarySums B h) →
      positiveLowerDensity (exactOrdinarySums B h) / hhpDenominator h ≤
        positiveLowerDensity (exactDistinctSums B h)

/-- Add zero for padding and then shift each allowed summand to a positive integer. -/
def paddedPositive (A : Set ℕ) : Set ℕ := Nat.succ '' (insert 0 A)

private theorem sum_map_succ (s : Multiset ℕ) : (s.map Nat.succ).sum = s.sum + s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]; omega

theorem eventually_exactOrdinary_padded {A : Set ℕ} {h : ℕ} (ha : HasOrder A h) :
    ∀ᶠ n : ℕ in atTop, n ∈ exactOrdinarySums (paddedPositive A) h := by
  obtain ⟨N₀, hN⟩ := eventually_atTop.mp ha
  apply eventually_atTop.mpr
  refine ⟨N₀ + h, ?_⟩
  intro n hn
  obtain ⟨s, hs, hc, hsum⟩ := hN (n-h) (by omega)
  let t := s + Multiset.replicate (h - s.card) 0
  have htc : t.card = h := by simp [t]; omega
  have hts : t.sum = n-h := by simp [t, hsum]
  refine ⟨t.map Nat.succ, ?_, by simpa using htc, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    apply Set.mem_image_of_mem
    rcases Multiset.mem_add.mp hy with hy | hy
    · exact Set.mem_insert_of_mem _ (hs y hy)
    · exact Set.mem_insert_iff.mpr (Or.inl (Multiset.eq_of_mem_replicate hy))
  · rw [sum_map_succ, hts, htc]
    omega

/-- Subtracting one from every distinct summand preserves distinctness. Erasing
zero, if present, gives a project witness using at most h elements of A. -/
theorem unshift_exactDistinct {A : Set ℕ} {h y : ℕ}
    (hy : y ∈ exactDistinctSums (paddedPositive A) h) :
    h ≤ y ∧ Rep A h (y - h) := by
  classical
  obtain ⟨s, hs, hcard, hsum⟩ := hy
  have hsucc (x : ℕ) (hx : x ∈ s) : (x-1) + 1 = x := by
    obtain ⟨a, _, rfl⟩ := hs x hx
    omega
  have hinj : Set.InjOn (fun x : ℕ => x-1) (s : Set ℕ) := by
    intro x hx z hz he
    have h₁ := hsucc x hx
    have h₂ := hsucc z hz
    change x - 1 = z - 1 at he
    omega
  let t := s.image (fun x => x-1)
  have htcard : t.card = h := (Finset.card_image_of_injOn hinj).trans hcard
  have ht : t.sum id + h = y := by
    change (s.image (fun x => x - 1)).sum id + h = y
    rw [Finset.sum_image (fun x hx z hz he => hinj hx hz he)]
    calc
      _ = (∑ x ∈ s, ((x - 1) + 1)) := by simp [Finset.sum_add_distrib, hcard]
      _ = s.sum id := Finset.sum_congr rfl (fun x hx => hsucc x hx)
      _ = y := hsum
  refine ⟨by omega, t.erase 0, ?_, (Finset.card_erase_le).trans htcard.le, ?_⟩
  · intro x hx
    obtain ⟨hne, hxt⟩ := Finset.mem_erase.mp hx
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hxt
    obtain ⟨a, ha, rfl⟩ := hs z hz
    have ex : a = x := by simpa using he
    rcases Set.mem_insert_iff.mp ha with hzero | hA
    · omega
    · exact ex ▸ hA
  · have he : (t.erase 0).sum id = t.sum id := by
      by_cases hzero : 0 ∈ t
      · simpa using (t.sum_erase_add id hzero)
      · rw [Finset.erase_eq_of_notMem hzero]
    omega

/-- The ordinary translated sumset contains a tail, which already gives
a uniform lower count with denominator 2. -/
theorem densityBound_of_tail {B : Set ℕ} (hb : ∀ᶠ n : ℕ in atTop, n ∈ B) :
    DensityBound B 2 := by
  classical
  obtain ⟨L, hL⟩ := eventually_atTop.mp hb
  refine ⟨2*L, ?_⟩
  intro N hN
  have hi : Finset.Ico L N ⊆ (Finset.range N).filter (· ∈ B) := by
    intro x hx
    obtain ⟨hl, hr⟩ := Finset.mem_Ico.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hL x hl⟩
  have hc := Finset.card_le_card hi
  rw [Nat.card_Ico] at hc
  omega

/-- Window form of unshifting. Since h is positive, an endpoint y=N
of the shifted interval maps to y-h inside the half-open project window. -/
theorem distinct_window_le_restricted {A : Set ℕ} {h : ℕ} (hh : 0 < h) (N : ℕ) :
    ((Finset.Icc 1 N).filter (· ∈ exactDistinctSums (paddedPositive A) h)).card ≤
      ((Finset.range N).filter (· ∈ restrictedSums A h)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun y => y - h)
  · intro y hy
    obtain ⟨hI, hdist⟩ := Finset.mem_filter.mp hy
    obtain ⟨hhy, hrep⟩ := unshift_exactDistinct hdist
    have hN := (Finset.mem_Icc.mp hI).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change y-h < N; omega), hrep⟩
  · intro y hy z hz he
    have h₁ := (unshift_exactDistinct (Finset.mem_filter.mp hy).2).1
    have h₂ := (unshift_exactDistinct (Finset.mem_filter.mp hz).2).1
    change y - h = z - h at he
    omega

/-- Read a strict lower-density bound as an eventual integer inequality. -/
theorem densityBound_of_shifted_density {A : Set ℕ} {h m : ℕ} (hh : 0 < h)
    (hm : 0 < m)
    (hd : 1 / (m : ℝ) < positiveLowerDensity (exactDistinctSums (paddedPositive A) h)) :
    DensityBound (restrictedSums A h) m := by
  classical
  let B := exactDistinctSums (paddedPositive A) h
  let C (N : ℕ) := ((Finset.Icc 1 N).filter (· ∈ B)).card
  have hfreq : ∀ᶠ N : ℕ in atTop, 1 / (m : ℝ) < (C N : ℝ) / N :=
    eventually_lt_of_lt_liminf hd (isBoundedUnder_of ⟨0, fun N => by positivity⟩)
  obtain ⟨L, hL⟩ := eventually_atTop.mp hfreq
  refine ⟨max L 1, ?_⟩
  intro N hN
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hineq := (div_lt_div_iff₀ hm' hpos).mp (hL N (by omega))
  have hcount : N ≤ m * C N := by
    exact_mod_cast (show (N : ℝ) ≤ (m : ℝ) * (C N : ℝ) by nlinarith [hineq])
  exact hcount.trans (Nat.mul_le_mul_left m (distinct_window_le_restricted hh N))

/-- HHP's single exact-sum inequality implies the project's density input.
The integer m is chosen from h before the basis A. -/
theorem uniformDensityInput_of_hhp (hhp : HHPDensityEstimate) : UniformDensityInput := by
  intro h hh
  have hhr : 0 < (h : ℝ) := by exact_mod_cast hh
  have hD : 0 < hhpDenominator h := by unfold hhpDenominator; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (4 * hhpDenominator h)
  have hm' : 0 < (m : ℝ) := by linarith
  have hm0 : 0 < m := by exact_mod_cast hm'
  refine ⟨m, hm0, ?_⟩
  intro A ha
  have hcount := densityBound_of_tail (eventually_exactOrdinary_padded ha)
  have hquarter : (1 / 4 : ℝ) < positiveLowerDensity (exactOrdinarySums (paddedPositive A) h) := by
    convert half_inv_lt_positiveLowerDensity (by decide : 0 < 2) hcount using 1 <;> norm_num
  have hBpos (x : ℕ) (hx : x ∈ paddedPositive A) : 0 < x := by
    obtain ⟨z, _, rfl⟩ := hx
    exact Nat.succ_pos _
  have hineq := hhp h hh (paddedPositive A) hBpos (by linarith)
  apply densityBound_of_shifted_density hh hm0
  calc
    1 / (m : ℝ) < (1/4 : ℝ) / hhpDenominator h := by
      rw [div_lt_div_iff₀ hm' hD]
      linarith
    _ ≤ _ := (div_le_div_of_nonneg_right hquarter.le hD.le).trans hineq

#print axioms uniformDensityInput_of_hhp

end Erdos338.Bridge
