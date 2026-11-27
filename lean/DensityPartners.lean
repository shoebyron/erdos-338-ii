import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Ring

/-! Finite counting in the quantitative restricted-sum density argument.
If each partial sum has at most h forbidden partners, any test set of more
than h partners gives every partial sum an allowed extension. -/

namespace Erdos338.Bridge

open scoped BigOperators

theorem exceptionalPartnerCount (B T G : Finset ℕ) (F : ℕ → Finset ℕ) (h : ℕ)
    (hcard : ∀ b ∈ B, (F b).card ≤ h) (hT : h < T.card)
    (allows : ∀ b ∈ B, ∀ a ∈ T, a ∉ F b → b + a ∈ G) :
    (B.biUnion (fun b => (F b).image (fun a => b + a))).card ≤ h * T.card * G.card := by
  classical
  let row (a : ℕ) := B.filter (fun b => a ∉ F b)
  have hcover : B ⊆ T.biUnion row := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.exists_mem_notMem_of_card_lt_card ((hcard b hb).trans_lt hT)
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
  have hr (a : ℕ) (ha : a ∈ T) : (row a).card ≤ G.card := by
    apply Finset.card_le_card_of_injOn (fun b : ℕ => b + a)
    · intro b hb
      obtain ⟨hbB, hf⟩ := Finset.mem_filter.mp hb
      exact allows b hbB a ha hf
    · intro b _ b' _ he
      exact Nat.add_right_cancel he
  have hB : B.card ≤ T.card * G.card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul T row G.card hr)
  calc
    _ ≤ B.card * h := Finset.card_biUnion_le_card_mul B _ h (fun b hb =>
      Finset.card_image_le.trans (hcard b hb))
    _ ≤ (T.card * G.card) * h := Nat.mul_le_mul_right _ hB
    _ = _ := by ac_rfl

#print axioms exceptionalPartnerCount

end Erdos338.Bridge
