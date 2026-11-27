import LemmaThree

/-! Chen–Yang–Zhao, Lemma 4, from the disjoint pair counts to the weighted
count on positive windows. The selected rank is allowed to vary with the window. -/
namespace Erdos338.Bridge

open Filter LemmaThree
open scoped BigOperators Classical

/-- Split by membership in the rich-sum set. The complementary window has
at most 2N elements because the rich-sum set contains zero. -/
theorem pair_count_bound (A : Set ℕ) (r Q N : ℕ) :
    let M := (window A r 1 N).card
    let e := (window A (r-1) 0 N).card
    let D := ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*r) Q)).card
    M^2 ≤ N*D + 8*r*(Q-1)*e*N + r*M*e := by
  classical
  let X := window A r 1 N
  let M := X.card
  let e := (window A (r-1) 0 N).card
  let p := pairCount X (chosenWitness A r)
  let C := richSums A (2*r) Q
  let S := Finset.range (2*N+1)
  let D := (S.filter (· ∈ C)).card
  let T := 4*r*(Q-1)*e
  have hMd : M ≤ N := by
    simpa [M, X, window] using
      Finset.card_filter_le (Finset.Icc 1 N) (· ∈ restrictedSums A r)
  obtain ⟨mass, pointwise, rich⟩ := lemma_three_chosen A r N
  have hzero : 0 ∈ C := Or.inl rfl
  have hcomp : (S.filter (· ∉ C)).card ≤ 2*N := by
    have hs : S.filter (· ∉ C) ⊆ Finset.Icc 1 (2*N) := by
      intro n hn
      obtain ⟨hnS, hnC⟩ := Finset.mem_filter.mp hn
      have hn' := Finset.mem_range.mp hnS
      have : n ≠ 0 := fun he => hnC (he ▸ hzero)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    simpa using Finset.card_le_card hs
  have richpart : (∑ n ∈ S.filter (· ∈ C), p n) ≤ D * N := by
    calc
      _ ≤ ∑ _n ∈ S.filter (· ∈ C), N :=
        Finset.sum_le_sum fun n _ => (pointwise n).trans hMd
      _ = _ := by simp [D]
  have poorpart : (∑ n ∈ S.filter (· ∉ C), p n) ≤ 2*N*T := by
    calc
      _ ≤ ∑ _n ∈ S.filter (· ∉ C), T := by
        apply Finset.sum_le_sum
        intro n hn
        by_contra! hp
        exact (Finset.mem_filter.mp hn).2 ((rich Q n hp).2)
      _ = (S.filter (· ∉ C)).card*T := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcomp
  have hpSum : (∑ n ∈ S, p n) ≤ N*D + 8*r*(Q-1)*e*N := by
    rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ C) p]
    calc
      _ ≤ D*N + 2*N*T := Nat.add_le_add richpart poorpart
      _ = _ := by unfold T; ring
  have hfinal : M^2 ≤ N*D + 8*r*(Q-1)*e*N + r*M*e :=
    mass.trans (Nat.add_le_add_right hpSum _)
  simpa only [D, S, Nat.range_succ_eq_Icc_zero] using hfinal

/-- Including zero adds at most one to the positive count. -/
private theorem count_zero_window_le (A : Set ℕ) (r N : ℕ) :
    (window A r 0 N).card ≤ (window A r 1 N).card + 1 := by
  classical
  have hs : window A r 0 N ⊆ insert 0 (window A r 1 N) := by
    intro n hn
    obtain ⟨hI, hx⟩ := Finset.mem_filter.mp hn
    by_cases hz : n = 0
    · simp [hz]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hI).2⟩, hx⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

private theorem zero_rank_card (A : Set ℕ) (N : ℕ) :
    (window A 0 1 N).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hI, hw⟩ := Finset.mem_filter.mp hn
  obtain ⟨w, _, hs, he⟩ := hw
  have : w = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
  simp [this] at he
  have := (Finset.mem_Icc.mp hI).1
  omega


private theorem exists_rank_transition (P : ℕ → Prop) (h : ℕ) (first : P 0) (last : ¬ P h) :
    ∃ t < h, P t ∧ ¬ P (t+1) := by
  classical
  induction h with
  | zero => exact (last first).elim
  | succ h ih =>
    by_cases hP : P h
    · exact ⟨h, Nat.lt_succ_self h, hP, last⟩
    · obtain ⟨t, ht, hgood, hnext⟩ := ih hP
      exact ⟨t, ht.trans (Nat.lt_succ_self h), hgood, hnext⟩

/-- Within each sufficiently large window there is a rank whose count is large
and whose predecessor has a small count (with zero included there). -/
theorem eventually_rank_transition (A : Set ℕ) (h m b : ℕ) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h,
      progressionAlpha h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ) ∧
      ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * progressionAlpha h m b (t+1) * N := by
  classical
  let den (t : ℕ) := (progressionStage h m b t).denominator
  let K := ∑ t ∈ Finset.range (h+1), den t
  have hevent : ∀ᶠ N : ℕ in atTop,
      progressionAlpha h m b 0 < ((window A h 1 N).card : ℝ) / N := by
    exact eventually_lt_of_lt_liminf hd (isBoundedUnder_of ⟨0, fun n => by positivity⟩)
  filter_upwards [hevent, eventually_ge_atTop K, eventually_gt_atTop 0] with N hfirst hN hpos
  have hlarge (t : ℕ) (ht : t ≤ h) : 1 ≤ progressionAlpha h m b t * (N : ℝ) := by
    have hden : den t ≤ N :=
      (Finset.single_le_sum (f := den) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : t < h+1))).trans hN
    have hdpos : 0 < (den t : ℝ) := by exact_mod_cast progressionDenominator_pos h m b t hm ht
    have hden' : (den t : ℝ) ≤ N := by exact_mod_cast hden
    change 1 ≤ 1 / (den t : ℝ) * N
    rwa [one_div, inv_mul_eq_div, le_div_iff₀ hdpos, one_mul]
  let P (t : ℕ) := progressionAlpha h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ)
  have first : P 0 := by
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hpos
    simpa [P] using ((lt_div_iff₀ hNpos).mp hfirst).le
  have last : ¬ P h := by
    intro ph
    have hzero : (window A (h-h) 1 N).card = 0 := by simp [zero_rank_card]
    change progressionAlpha h m b h * (N : ℝ) ≤ _ at ph
    rw [hzero, Nat.cast_zero] at ph
    linarith [hlarge h le_rfl]
  obtain ⟨t, ht, htgood, htbad⟩ := exists_rank_transition P h first last
  refine ⟨t, ht, htgood, ?_⟩
  have hprev : h-(t+1) = h-t-1 := by omega
  change ¬ progressionAlpha h m b (t+1) * N ≤ ((window A (h-(t+1)) 1 N).card : ℝ) at htbad
  rw [hprev, not_le] at htbad
  have hc : ((window A (h-t-1) 0 N).card : ℝ) ≤ ((window A (h-t-1) 1 N).card : ℝ) + 1 := by
    exact_mod_cast count_zero_window_le A (h-t-1) N
  linarith [hlarge (t+1) (by omega)]

/-- The weighted count at a good rank, using the numerical step of Lemma 4
on the actual disjoint-pair estimates of Lemma 3. -/
theorem weighted_rank_at (A : Set ℕ) (h m b t N : ℕ) (hm : 0 < m) (ht : t < h) (hN : 0 < N)
    (hM : progressionAlpha h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ))
    (he : ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * progressionAlpha h m b (t+1) * N) :
    6 * N ≤ progressionL h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (progressionQ h m b t))).card := by
  classical
  let r := h-t
  let Q := progressionQ h m b t
  let L := progressionL h m b t
  let α := progressionAlpha h m b t
  let M := (window A r 1 N).card
  let e := (window A (r-1) 0 N).card
  let D := ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*r) Q)).card
  have hQ : 0 < Q := Nat.zero_lt_succ _
  have hr : 0 < r := Nat.sub_pos_of_lt ht
  have hcap : M ≤ N := by
    simpa [M, window] using Finset.card_filter_le (Finset.Icc 1 N) (· ∈ restrictedSums A r)
  have hb : M^2 ≤ N*D + 8*r*(Q-1)*e*N + r*M*e := pair_count_bound A r Q N
  have hb' : (M : ℝ)^2 ≤ (N : ℝ)*D + 8*(r : ℝ)*((Q-1 : ℕ) : ℝ)*e*N + (r : ℝ)*M*e := by
    exact_mod_cast hb
  rw [Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one] at hb'
  obtain ⟨hα, hL, _, hnext⟩ := progression_equation_two h m b t hm ht
  rw [hnext] at he
  have hceil : 8 / α^2 ≤ (L : ℝ) := by
    change 8 / progressionAlpha h m b t ^ 2 ≤ (progressionL h m b t : ℝ)
    rw [hL]; exact Nat.le_ceil _
  have hcount : (M : ℝ)^2 - (r : ℝ)*M*e ≤ (N : ℝ)*D + 8*(r : ℝ)*((Q : ℝ)-1)*e*N := by
    linarith only [hb']
  have result := (progression_many_popular_sums N r Q α L M e D
    (by exact_mod_cast hN) (by exact_mod_cast hr) (by exact_mod_cast hQ) hα (by positivity)
    hM (by exact_mod_cast hcap) he hcount hceil).2
  exact_mod_cast result

/-- The rank is selected after the window size. Summing across ranks gives the
uniform lower bound without fixing a single rank for all large windows. -/
theorem eventually_weighted_rank (A : Set ℕ) (h m b : ℕ) (_hh : 0 < h) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h, 6*N ≤ progressionL h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (progressionQ h m b t))).card := by
  filter_upwards [eventually_rank_transition A h m b hm hd, eventually_gt_atTop 0] with N hgood hN
  obtain ⟨t, ht, hM, he⟩ := hgood
  exact ⟨t, ht, weighted_rank_at A h m b t N hm ht hN hM he⟩

#print axioms eventually_weighted_rank
end Erdos338.Bridge
