import ProductiveWindow
import TwoScale
import CommonWindows
import PaddedEmbedding
import CollisionDensity

/-! The production estimate permits a different rank at every window.
Finite cyclic covering at two adjacent window sizes supplies a tail of the
zero residue class. The schedule reserves enough copies for both windows. -/

namespace Erdos338.Bridge

open Filter
open scoped Pointwise Classical

/-- A uniform number of distinct summands survives every allowed deletion.
Only the modulus and the start of its progression depend on the underlying set. -/
theorem uniformProgressionInput : UniformProgressionInput := by
  intro h m b hh hm
  let allow := fun l => 2 * twoScaleCap l
  refine ⟨paddedK allow h m b, ?_⟩
  intro A hden
  let C := fun t => richSums A (2*(h-t)) (paddedQ allow h m b t)
  let L := paddedL allow h m b
  have h0 (i : ℕ) : 0 ∈ C i := Or.inl rfl
  have hdens : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h) := by
    rw [progressionAlpha_zero]
    exact half_inv_lt_positiveLowerDensity hm hden
  have mass : ∀ᶠ X : ℕ in atTop, ∃ i < h, 6*X ≤ L i * windowCount (C i) (2*X) :=
    eventually_padded_rank allow A h m b hh hm hdens
  obtain ⟨d, hd, windows⟩ := synchronizeProductiveWindows h C L
    (fun i hi => localCoverAtProductiveWindows (C i) (h0 i) (L i)
      (paddedL_pos allow h m b i hm hi.le)) mass
  obtain ⟨g, hg, hn⟩ := twoScaleCover h C L d hd (fun i _ => h0 i) windows
  obtain ⟨N₀, hN⟩ := eventually_atTop.mp hn
  refine ⟨g, hg, 0, N₀, ?_⟩
  intro F _ hF n hn hnmod
  obtain ⟨i, hi, j, hj, u, hu, v, hv, huv⟩ :=
    hN n hn ((ZMod.natCast_eq_zero_iff n g).mp hnmod)
  apply rep_paddedSums allow F hF h n
  rw [← huv]
  exact two_mem_paddedSums twoScaleCap A h m b i j u v hi hj hu hv

/-- Erdős #338(ii), using the two unconditional inputs to the verified bridge. -/
theorem boundedByOrder : BoundedByOrder :=
  boundedByOrder_of_analyticInputs uniformDensityInput uniformProgressionInput

#check Erdos338.Bridge.boundedByOrder
#print axioms Erdos338.Bridge.uniformProgressionInput
#print axioms Erdos338.Bridge.boundedByOrder

end Erdos338.Bridge

