import UniformProgression
import InfiniteLevels

/-!
# Infinite sumsets in the progression proof

The list in Chen–Yang–Zhao, Lemma 1, may contain repetitions. We turn the
infinite ranks of Lemma 4 into precisely that list and identify its pointwise
sum and its counting function. The density form of Kneser's theorem is a
proposition here; every theorem using it takes a proof as an explicit argument.
-/

namespace Erdos338.Bridge
open Filter
open scoped Pointwise Classical

/-- Chen–Yang–Zhao, Lemma 1, on lower asymptotic density (arXiv:2611.33191v1).
The limit inferior is taken *after* adding the individual counting functions. -/
def AsymptoticKneser : Prop :=
  ∀ X : List (Set ℕ), 2 ≤ X.length → (∀ C ∈ X, C.Infinite) →
    positiveLowerDensity X.sum <
      liminf (fun N : ℕ =>
        (((X.map (fun C => windowCount C N)).sum : ℕ) : ℝ) / N) atTop →
    ∃ g : ℕ, 0 < g ∧ ∃ T : Set (ZMod g),
      ∀ᶠ n : ℕ in atTop, n ∈ X.sum ↔ (n : ZMod g) ∈ T

noncomputable def infiniteSummands (C : ℕ → Set ℕ) (L : ℕ → ℕ) : ℕ → List (Set ℕ)
  | 0 => []
  | t+1 => if (C t).Infinite then infiniteSummands C L t ++ List.replicate (L t) (C t)
           else infiniteSummands C L t

theorem infiniteSummands_infinite (C : ℕ → Set ℕ) (L : ℕ → ℕ) (t : ℕ) :
    ∀ S ∈ infiniteSummands C L t, S.Infinite := by
  induction t with
  | zero => simp [infiniteSummands]
  | succ t ih =>
    by_cases ht : (C t).Infinite
    · intro S hS
      rw [infiniteSummands, ite_eq_left ht, List.mem_append] at hS
      rcases hS with h | h
      · exact ih S h
      · obtain ⟨_, he⟩ := List.mem_replicate.mp h
        simpa only [he] using ht
    · simpa only [infiniteSummands, ht, ↓reduceIte] using ih

theorem infiniteSummands_total (C : ℕ → Set ℕ) (L : ℕ → ℕ) (t : ℕ) (f : Set ℕ → ℕ) :
    ((infiniteSummands C L t).map f).sum =
      ∑ j ∈ (Finset.range t).filter (fun j => (C j).Infinite), L j * f (C j) := by
  induction t with
  | zero => simp [infiniteSummands]
  | succ t ih =>
    rw [Finset.sum_filter, Finset.sum_range_succ, ← Finset.sum_filter]
    by_cases ht : (C t).Infinite <;>
      simp [infiniteSummands, ht, ih, List.sum_replicate]

theorem infiniteSummands_length (C : ℕ → Set ℕ) (L : ℕ → ℕ) (t : ℕ) :
    (infiniteSummands C L t).length =
      ∑ j ∈ (Finset.range t).filter (fun j => (C j).Infinite), L j := by
  simpa using infiniteSummands_total C L t (fun _ => 1)

theorem addCopies_eq_pointwise (B C : Set ℕ) (k : ℕ) :
    addCopies B C k = B + k • C := by
  induction k with
  | zero => simp [addCopies]
  | succ k ih =>
    rw [succ_nsmul, ← add_assoc, ← ih]
    rfl

theorem infiniteSummands_sum (A : Set ℕ) (h m b t : ℕ) :
    (infiniteSummands (fun j => richSums A (2 * (h - j)) (progressionQ h m b j))
      (progressionL h m b) t).sum = infiniteLevelSums A h m b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases hi : (richSums A (2 * (h - t)) (progressionQ h m b t)).Infinite
    · simp [infiniteSummands, infiniteLevelSums, hi, ih, List.sum_replicate,
        addCopies_eq_pointwise]
    · simp [infiniteSummands, infiniteLevelSums, hi, ih]

theorem positiveLowerDensity_le_one (B : Set ℕ) : positiveLowerDensity B ≤ 1 := by
  unfold positiveLowerDensity
  apply liminf_le_of_frequently_le
  · apply Eventually.frequently
    filter_upwards [eventually_gt_atTop 0] with N hN
    apply (div_le_iff₀ (by exact_mod_cast hN : 0 < (N : ℝ))).mpr
    rw [one_mul]
    exact_mod_cast (show ((Finset.Icc 1 N).filter (· ∈ B)).card ≤ N by
      simpa using (Finset.card_filter_le (Finset.Icc 1 N) (fun x => x ∈ B)))
  · refine ⟨(0 : ℝ), ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ (((Finset.Icc 1 N).filter (· ∈ B)).card : ℝ) / N
    exact Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end Erdos338.Bridge
