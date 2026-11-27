import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The lower limit over the infinite levels in Chen–Yang–Zhao, Lemma 4.
The successful level is allowed to depend on the window. -/

namespace Erdos338.Bridge

open Filter
open scoped BigOperators Classical

/-- Count a set of natural numbers in the closed window [0,N]. -/
noncomputable def windowCount (B : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 0 N).filter (· ∈ B)).card

/-- Indices with infinite summand sets. Only these occur in the infinite sumset. -/
noncomputable def infiniteRanks (C : ℕ → Set ℕ) (h : ℕ) : Finset ℕ :=
  (Finset.range h).filter (fun t => (C t).Infinite)

/-- Count every summand set in the indexed family with its prescribed multiplicity. -/
noncomputable def weightedCount (C : ℕ → Set ℕ) (L : ℕ → ℕ) (I : Finset ℕ) (N : ℕ) : ℕ :=
  ∑ t ∈ I, L t * windowCount (C t) N

theorem windowCount_mono (B : Set ℕ) : Monotone (windowCount B) := by
  intro i j hij
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxI, hB⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hxI).2.trans hij⟩, hB⟩

theorem weightedCount_mono (C : ℕ → Set ℕ) (L : ℕ → ℕ) (I : Finset ℕ) :
    Monotone (weightedCount C L I) := by
  intro i j hij
  exact Finset.sum_le_sum (fun t _ => Nat.mul_le_mul_left _ (windowCount_mono (C t) hij))

private theorem windowCount_le_ncard {B : Set ℕ} (hf : B.Finite) (N : ℕ) :
    windowCount B N ≤ B.ncard := by
  unfold windowCount
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun x hx => (Finset.mem_filter.mp hx).2) hf

/-- A finite level has uniformly bounded contribution. For sufficiently large N,
any level meeting the 6N bound is infinite. It can still vary with N. -/
theorem eventually_infinite_rank_of_mass (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    ∀ᶠ N : ℕ in atTop, ∃ t ∈ infiniteRanks C h, 6 * N ≤ L t * windowCount (C t) (2 * N) := by
  let B := ∑ t ∈ Finset.range h, L t * (C t).ncard
  filter_upwards [mass, eventually_ge_atTop (B + 1)] with N hm hN
  obtain ⟨t, ht, hmass⟩ := hm
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, ?_⟩, hmass⟩
  intro hfinite
  have hcard := Nat.mul_le_mul_left (L t) (windowCount_le_ncard hfinite (2 * N))
  have hbound : L t * (C t).ncard ≤ B :=
    Finset.single_le_sum (f := fun j => L j * (C j).ncard)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
  omega

/-- Total weight on infinite levels at an even window is at least three times its width. -/
theorem eventually_even_weightedCount (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    ∀ᶠ N : ℕ in atTop, 6 * N ≤ weightedCount C L (infiniteRanks C h) (2 * N) := by
  filter_upwards [eventually_infinite_rank_of_mass C L h mass] with N hn
  obtain ⟨t, ht, hm⟩ := hn
  exact hm.trans (Finset.single_le_sum (f := fun j => L j * windowCount (C j) (2 * N))
    (fun _ _ => Nat.zero_le _) ht)

/-- Odd windows lose at most three in the numerator relative to the even-window bound. -/
theorem eventually_weightedCount_add_three (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    ∀ᶠ N : ℕ in atTop, 3 * N ≤ weightedCount C L (infiniteRanks C h) N + 3 := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_even_weightedCount C L h mass)
  filter_upwards [eventually_ge_atTop (2 * K)] with N hN
  have heven := hK (N / 2) (by omega)
  have hm := weightedCount_mono C L (infiniteRanks C h)
    (show 2 * (N / 2) ≤ N by omega)
  omega

private theorem weightedCount_le (C : ℕ → Set ℕ) (L : ℕ → ℕ) (I : Finset ℕ) (N : ℕ) :
    weightedCount C L I N ≤ (∑ t ∈ I, L t) * (N + 1) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t _
  apply Nat.mul_le_mul_left
  simpa [windowCount] using Finset.card_filter_le (Finset.Icc 0 N) (fun x => x ∈ C t)

/-- Lemma 4's lower-limit bound with exactly the infinite summand sets retained. -/
theorem three_le_infinite_liminf (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    (3 : ℝ) ≤ liminf (fun N : ℕ => (weightedCount C L (infiniteRanks C h) N : ℝ) / N) atTop := by
  let I := infiniteRanks C h
  let W := ∑ t ∈ I, L t
  have hupper : ∀ N : ℕ, (weightedCount C L I N : ℝ) / N ≤ 2 * (W : ℝ) := by
    intro N
    by_cases hz : N = 0
    · simp [hz]
    · have hp : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      apply (div_le_iff₀ hp).2
      have hcard := weightedCount_le C L I N
      have hu : W * (N + 1) ≤ (2 * W) * N := by
        calc
          _ ≤ W * (2 * N) := Nat.mul_le_mul_left _ (by omega)
          _ = _ := by ac_rfl
      exact_mod_cast hcard.trans hu
  have hlower : IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ => (weightedCount C L I N : ℝ) / N) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ (weightedCount C L I N : ℝ) / N
    exact Eventually.of_forall fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 2 * (W : ℝ)) _ hupper) hlower).mpr
  intro y hy
  obtain ⟨K, hK⟩ := exists_nat_gt (3 / (3 - y))
  filter_upwards [eventually_weightedCount_add_three C L h mass, eventually_ge_atTop K,
    eventually_ge_atTop 1] with N hm hN hpos
  have hp : 0 < (N : ℝ) := by exact_mod_cast hpos
  apply (lt_div_iff₀ hp).2
  have hK' := hK.trans_le (show (K : ℝ) ≤ N by exact_mod_cast hN)
  have hg := (div_lt_iff₀ (sub_pos.mpr hy)).mp hK'
  have hc : 3 * (N : ℝ) ≤ (weightedCount C L I N : ℝ) + 3 := by exact_mod_cast hm
  nlinarith

theorem infiniteRanks_nonempty (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    (infiniteRanks C h).Nonempty := by
  obtain ⟨_, t, ht, _⟩ := (eventually_infinite_rank_of_mass C L h mass).exists
  exact ⟨t, ht⟩

theorem two_le_infinite_multiplicity (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N))
    (hL : ∀ t < h, 2 ≤ L t) : 2 ≤ ∑ t ∈ infiniteRanks C h, L t := by
  obtain ⟨t, ht⟩ := infiniteRanks_nonempty C L h mass
  exact (hL t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)).trans
    (Finset.single_le_sum (f := L) (fun _ _ => Nat.zero_le _) ht)

#print axioms three_le_infinite_liminf

end Erdos338.Bridge
