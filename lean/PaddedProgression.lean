import WeightedCount

/-! An enlarged slot budget for the window argument. The density weight L and
the number of available summands B are separate. Choosing B as a function of L
before descending to the next rank keeps the entire schedule independent of A. -/
namespace Erdos338.Bridge

open Filter LemmaThree
open scoped BigOperators Classical

def paddedMultiplicity (allow : ℕ → ℕ) (s : ProgressionStage) (r b : ℕ) : ℕ :=
  b + s.cost + 2 * r * (allow s.length - 1) + 1

def paddedStage (allow : ℕ → ℕ) (h m b : ℕ) : ℕ → ProgressionStage
  | 0 => ⟨2*m, 0⟩
  | t+1 =>
    let s := paddedStage allow h m b t
    let r := h-t
    ⟨s.denominator ^ 2 * (64*r*paddedMultiplicity allow s r b),
     s.cost + 2*r*allow s.length⟩

noncomputable def paddedAlpha (allow : ℕ → ℕ) (h m b t : ℕ) : ℝ :=
  1 / ((paddedStage allow h m b t).denominator : ℝ)

def paddedL (allow : ℕ → ℕ) (h m b t : ℕ) : ℕ := (paddedStage allow h m b t).length
def paddedB (allow : ℕ → ℕ) (h m b t : ℕ) : ℕ := allow (paddedL allow h m b t)
def paddedQ (allow : ℕ → ℕ) (h m b t : ℕ) : ℕ :=
  paddedMultiplicity allow (paddedStage allow h m b t) (h-t) b
def paddedK (allow : ℕ → ℕ) (h m b : ℕ) : ℕ := (paddedStage allow h m b h).cost

theorem paddedDenominator_pos (allow : ℕ → ℕ) (h m b t : ℕ) (hm : 0 < m) (ht : t ≤ h) :
    0 < (paddedStage allow h m b t).denominator := by
  induction t with
  | zero => change 0 < 2*m; positivity
  | succ t ih =>
    have hd := ih (by omega)
    have hr : 0 < h-t := by omega
    have hq : 0 < paddedMultiplicity allow (paddedStage allow h m b t) (h-t) b := Nat.zero_lt_succ _
    change 0 < (paddedStage allow h m b t).denominator ^ 2 *
      (64 * (h-t) * paddedMultiplicity allow (paddedStage allow h m b t) (h-t) b)
    positivity

theorem paddedL_pos (allow : ℕ → ℕ) (h m b t : ℕ) (hm : 0 < m) (ht : t ≤ h) :
    0 < paddedL allow h m b t := by
  have := paddedDenominator_pos allow h m b t hm ht
  unfold paddedL ProgressionStage.length
  positivity

theorem padded_equation (allow : ℕ → ℕ) (h m b t : ℕ) (hm : 0 < m) (ht : t < h) :
    0 < paddedAlpha allow h m b t ∧
    paddedL allow h m b t = ⌈8 / paddedAlpha allow h m b t ^ 2⌉₊ ∧
    paddedAlpha allow h m b (t+1) =
      paddedAlpha allow h m b t ^ 2 / (64 * ((h-t : ℕ) : ℝ) * paddedQ allow h m b t) := by
  have hd := paddedDenominator_pos allow h m b t hm ht.le
  refine ⟨by unfold paddedAlpha; positivity, ?_, ?_⟩
  · have he : 8 / paddedAlpha allow h m b t ^ 2 = ((paddedL allow h m b t : ℕ) : ℝ) := by
      simp [paddedAlpha, paddedL, ProgressionStage.length]
    rw [he, Nat.ceil_natCast]
  · simp [paddedAlpha, paddedStage, paddedQ, div_eq_mul_inv, mul_inv_rev,
      mul_comm, mul_left_comm, mul_assoc]

/-- Including zero adds at most one to the positive count. -/
private theorem padded_zero_window_le (A : Set ℕ) (r N : ℕ) :
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

private theorem padded_zero_rank_card (A : Set ℕ) (N : ℕ) :
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


private theorem padded_exists_rank_transition (P : ℕ → Prop) (h : ℕ) (first : P 0) (last : ¬ P h) :
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
theorem eventually_padded_transition (allow : ℕ → ℕ) (A : Set ℕ) (h m b : ℕ) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h,
      paddedAlpha allow h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ) ∧
      ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * paddedAlpha allow h m b (t+1) * N := by
  classical
  let den (t : ℕ) := (paddedStage allow h m b t).denominator
  let K := ∑ t ∈ Finset.range (h+1), den t
  have hevent : ∀ᶠ N : ℕ in atTop,
      progressionAlpha h m b 0 < ((window A h 1 N).card : ℝ) / N := by
    exact eventually_lt_of_lt_liminf hd (isBoundedUnder_of ⟨0, fun n => by positivity⟩)
  filter_upwards [hevent, eventually_ge_atTop K, eventually_gt_atTop 0] with N hfirst hN hpos
  have hlarge (t : ℕ) (ht : t ≤ h) : 1 ≤ paddedAlpha allow h m b t * (N : ℝ) := by
    have hden : den t ≤ N :=
      (Finset.single_le_sum (f := den) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : t < h+1))).trans hN
    have hdpos : 0 < (den t : ℝ) := by exact_mod_cast paddedDenominator_pos allow h m b t hm ht
    have hden' : (den t : ℝ) ≤ N := by exact_mod_cast hden
    change 1 ≤ 1 / (den t : ℝ) * N
    rwa [one_div, inv_mul_eq_div, le_div_iff₀ hdpos, one_mul]
  let P (t : ℕ) := paddedAlpha allow h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ)
  have first : P 0 := by
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hpos
    simpa [P, paddedAlpha, paddedStage, progressionAlpha, progressionStage] using ((lt_div_iff₀ hNpos).mp hfirst).le
  have last : ¬ P h := by
    intro ph
    have hzero : (window A (h-h) 1 N).card = 0 := by simp [padded_zero_rank_card]
    change paddedAlpha allow h m b h * (N : ℝ) ≤ _ at ph
    rw [hzero, Nat.cast_zero] at ph
    linarith [hlarge h le_rfl]
  obtain ⟨t, ht, htgood, htbad⟩ := padded_exists_rank_transition P h first last
  refine ⟨t, ht, htgood, ?_⟩
  have hprev : h-(t+1) = h-t-1 := by omega
  change ¬ paddedAlpha allow h m b (t+1) * N ≤ ((window A (h-(t+1)) 1 N).card : ℝ) at htbad
  rw [hprev, not_le] at htbad
  have hc : ((window A (h-t-1) 0 N).card : ℝ) ≤ ((window A (h-t-1) 1 N).card : ℝ) + 1 := by
    exact_mod_cast padded_zero_window_le A (h-t-1) N
  linarith [hlarge (t+1) (by omega)]

/-- The weighted count at a good rank, using the numerical step of Lemma 4
on the actual disjoint-pair estimates of Lemma 3. -/
theorem padded_rank_at (allow : ℕ → ℕ) (A : Set ℕ) (h m b t N : ℕ) (hm : 0 < m) (ht : t < h) (hN : 0 < N)
    (hM : paddedAlpha allow h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ))
    (he : ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * paddedAlpha allow h m b (t+1) * N) :
    6 * N ≤ paddedL allow h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (paddedQ allow h m b t))).card := by
  classical
  let r := h-t
  let Q := paddedQ allow h m b t
  let L := paddedL allow h m b t
  let α := paddedAlpha allow h m b t
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
  obtain ⟨hα, hL, hnext⟩ := padded_equation allow h m b t hm ht
  rw [hnext] at he
  have hceil : 8 / α^2 ≤ (L : ℝ) := by
    change 8 / paddedAlpha allow h m b t ^ 2 ≤ (paddedL allow h m b t : ℝ)
    rw [hL]; exact Nat.le_ceil _
  have hcount : (M : ℝ)^2 - (r : ℝ)*M*e ≤ (N : ℝ)*D + 8*(r : ℝ)*((Q : ℝ)-1)*e*N := by
    linarith only [hb']
  have result := (progression_many_popular_sums N r Q α L M e D
    (by exact_mod_cast hN) (by exact_mod_cast hr) (by exact_mod_cast hQ) hα (by positivity)
    hM (by exact_mod_cast hcap) he hcount hceil).2
  exact_mod_cast result

/-- The rank is selected after the window size. Summing across ranks gives the
uniform lower bound without fixing a single rank for all large windows. -/
theorem eventually_padded_rank (allow : ℕ → ℕ) (A : Set ℕ) (h m b : ℕ) (_hh : 0 < h) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h, 6*N ≤ paddedL allow h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (paddedQ allow h m b t))).card := by
  filter_upwards [eventually_padded_transition allow A h m b hm hd, eventually_gt_atTop 0] with N hgood hN
  obtain ⟨t, ht, hM, he⟩ := hgood
  exact ⟨t, ht, padded_rank_at allow A h m b t N hm ht hN hM he⟩

private theorem padded_chooseOutside {A : Set ℕ} {w q d : ℕ} (hd : d ∈ richSums A w q)
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

private theorem padded_rep_addCopies {A B : Set ℕ} {F : Finset ℕ} {p w q L : ℕ}
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
    obtain ⟨G, hG, hg, hdsum, hdis⟩ := padded_chooseOutside hd (F ∪ T) hroom
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
def paddedSums (allow : ℕ → ℕ) (A : Set ℕ) (h m b : ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | t + 1 => addCopies (paddedSums allow A h m b t)
      (richSums A (2 * (h - t)) (paddedQ allow h m b t)) (paddedB allow h m b t)

/-- Greedy disjoint representatives, equations (4) and (5), at any prefix of the levels. -/
theorem rep_paddedSums (allow : ℕ → ℕ) {A : Set ℕ} {h m b : ℕ} (F : Finset ℕ) (hf : F.card ≤ b)
    (t : ℕ) : ∀ n ∈ paddedSums allow A h m b t,
      Rep (A \ (F : Set ℕ)) (paddedStage allow h m b t).cost n := by
  induction t with
  | zero =>
    intro n hn
    have he : n = 0 := hn
    exact ⟨∅, by simp, by simp, by simp [he]⟩
  | succ t ih =>
    apply padded_rep_addCopies ih _ _ (le_refl _)
    change F.card + _ + _ < b + (paddedStage allow h m b t).cost +
      2 * (h - t) * (paddedB allow h m b t - 1) + 1
    omega


#print axioms eventually_padded_rank
#print axioms rep_paddedSums
end Erdos338.Bridge
