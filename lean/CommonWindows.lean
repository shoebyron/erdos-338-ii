import InfiniteLevels
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Order.Filter.Finite

namespace Erdos338.Bridge

open Filter
open scoped Pointwise Classical

/-- Choose one period per rank before selecting a productive rank at a window.
The existence of the window threshold is uniform over this finite collection of ranks. -/
theorem synchronizeProductiveWindows
    (h : ℕ) (C : ℕ → Set ℕ) (L : ℕ → ℕ)
    (cover : ∀ i < h, ∃ d : ℕ, 0 < d ∧ ∀ᶠ X : ℕ in atTop,
      6*X ≤ L i * windowCount (C i) (2*X) →
      ∃ ℓ ∈ C i, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L i * ℓ ∧ d ≤ L i ∧
        ∀ u k : ℕ, d ∣ u → (4*(L i+1))*ℓ ≤ u →
          u + (4*(L i+1))*ℓ ≤ k*ℓ → u ∈ k • C i)
    (mass : ∀ᶠ X : ℕ in atTop, ∃ i < h, 6*X ≤ L i * windowCount (C i) (2*X)) :
    ∃ d : ℕ → ℕ, (∀ i < h, 0 < d i) ∧ ∀ᶠ X : ℕ in atTop,
      ∃ i < h, ∃ ℓ ∈ C i, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L i * ℓ ∧ d i ≤ L i ∧
        ∀ u k : ℕ, d i ∣ u → (4*(L i+1))*ℓ ≤ u →
          u + (4*(L i+1))*ℓ ≤ k*ℓ → u ∈ k • C i := by
  classical
  let d := fun i => if hi : i < h then (cover i hi).choose else 1
  have pos (i : ℕ) (hi : i < h) : 0 < d i := by
    simpa [d, hi] using (cover i hi).choose_spec.1
  have per (i : ℕ) (hi : i ∈ Finset.range h) :
      ∀ᶠ X : ℕ in atTop, 6*X ≤ L i * windowCount (C i) (2*X) →
        ∃ ℓ ∈ C i, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L i * ℓ ∧ d i ≤ L i ∧
          ∀ u k : ℕ, d i ∣ u → (4*(L i+1))*ℓ ≤ u →
            u + (4*(L i+1))*ℓ ≤ k*ℓ → u ∈ k • C i := by
    have ht := Finset.mem_range.mp hi
    simpa [d, ht] using (cover i ht).choose_spec.2
  refine ⟨d, pos, ?_⟩
  filter_upwards [mass, ((Finset.range h).eventually_all).2 per] with X good all
  obtain ⟨i, hi, hm⟩ := good
  exact ⟨i, hi, all i (Finset.mem_range.mpr hi) hm⟩

end Erdos338.Bridge

