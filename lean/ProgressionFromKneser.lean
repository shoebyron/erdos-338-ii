import WeightedCount
import KneserFamily

/-! Apply the infinite-summand density estimate to the literal list of sets in
Chen–Yang–Zhao's Lemma 1. -/

namespace Erdos338.Bridge
open Filter
open scoped Pointwise Classical

theorem progressionInput_of_asymptoticKneser (kneser : AsymptoticKneser) :
    UniformProgressionInput := by
  apply uniformProgressionInput_of_periodicity
  intro h m b hh hm A hd
  let C := fun t => richSums A (2 * (h - t)) (progressionQ h m b t)
  let L := progressionL h m b
  let X := infiniteSummands C L h
  have mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N) :=
    eventually_weighted_rank A h m b hh hm hd
  obtain ⟨u, hu⟩ := infiniteRanks_nonempty C L h mass
  obtain ⟨hu', hCi⟩ := Finset.mem_filter.mp hu
  refine ⟨infiniteLevelSums_infinite hm (Finset.mem_range.mp hu') hCi, ?_⟩
  have hL (t : ℕ) (ht : t < h) : 2 ≤ L t := by
    have hD := progressionDenominator_pos h m b t hm ht.le
    change 2 ≤ 8 * (progressionStage h m b t).denominator ^ 2
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hD),
      Nat.one_le_pow 2 _ hD]
  have hlen : 2 ≤ X.length := by
    rw [show X.length = _ from infiniteSummands_length C L h]
    exact two_le_infinite_multiplicity C L h mass hL
  have hsum : X.sum = infiniteLevelSums A h m b h := infiniteSummands_sum A h m b h
  have hcounts (N : ℕ) :
      (X.map (fun S => windowCount S N)).sum = weightedCount C L (infiniteRanks C h) N :=
    infiniteSummands_total C L h (fun S => windowCount S N)
  have hlarge : positiveLowerDensity X.sum <
      liminf (fun N : ℕ => ((X.map (fun S => windowCount S N)).sum : ℝ) / N) atTop := by
    simp only [hcounts]
    exact (positiveLowerDensity_le_one _).trans_lt
      ((by norm_num : (1 : ℝ) < 3).trans_le (three_le_infinite_liminf C L h mass))
  obtain ⟨g, hg, T, hp⟩ := kneser X hlen (infiniteSummands_infinite C L h) hlarge
  exact ⟨g, hg, T, hsum ▸ hp⟩

#print axioms progressionInput_of_asymptoticKneser

end Erdos338.Bridge
