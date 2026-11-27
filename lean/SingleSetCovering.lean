import Mathlib
import MiscYD.AddCombi.Kneser.Kneser

/-!
Finite cyclic covering and arithmetic progressions for a single dense set.
Adapted from Daniel Veljjanoski's erdos338-palomar, files Covering, Structure,
and Shift, commit a699263d0f7cdce0e5b3026bce86eab30973d0f8.
https://github.com/veljjanoski/erdos338-palomar
The port uses the pinned MiscYD Kneser theorem supplied by the project.
Distributed under the Apache License, Version 2.0 (included below).
-/
/-!
# Sums of many copies of a dense finite set

Kneser's theorem for `h` summands, and its consequence for a set `A ⊆ [0, ℓ]` containing `0` and
`ℓ`: if `A` is not too small and its image generates `ZMod ℓ`, every residue mod `ℓ` is a sum of
`h` elements of `A`, and so every integer in `[h ℓ, (m - h) ℓ]` is a sum of exactly `m` elements
of `A`.
-/

open Finset
open scoped Pointwise

namespace Erdos338Proof

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- `h • (s + H) = h • s + H` when `H + H = H`. -/
lemma nsmul_add_stab (s H : Finset G) (hH : H + H = H) {h : ℕ} (hh : 1 ≤ h) :
    h • (s + H) = h • s + H := by
  induction h, hh using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [succ_nsmul, ih, succ_nsmul]
    calc n • s + H + (s + H) = n • s + s + (H + H) := by abel
      _ = n • s + s + H := by rw [hH]

/-- **Kneser's theorem for `h` summands**: with `H` the stabilizer of `h • s`,
`h |s + H| ≤ |h • s| + (h - 1) |H|`. -/
lemma kneser_nsmul {h : ℕ} (hh : 1 ≤ h) :
    ∀ s : Finset G, s.Nonempty →
      h * #(s + (h • s).addStab) ≤ #(h • s) + (h - 1) * #(h • s).addStab := by
  induction h, hh using Nat.le_induction with
  | base =>
    intro s _
    simp [add_addStab]
  | succ n hn ih =>
    intro s hs
    set H := ((n + 1) • s).addStab with hHdef
    have hns : (n • s).Nonempty := hs.nsmul
    have hn1 : ((n + 1) • s).Nonempty := hs.nsmul
    have hHH : H + H = H := addStab_add_addStab _
    have hsH : (s + H).Nonempty := hs.add hn1.addStab
    -- the stabilizer of `n • (s + H) = n • s + H` is `H`
    have hnsH : n • (s + H) = n • s + H := nsmul_add_stab s H hHH hn
    have hstab : (n • (s + H)).addStab = H := by
      rw [hnsH]
      apply le_antisymm
      · calc (n • s + H).addStab ⊆ (n • s + H + s).addStab := subset_addStab_add_left hs
          _ = ((n + 1) • s + H).addStab := by rw [succ_nsmul]; congr 1; abel
          _ = H := by rw [add_addStab]
      · calc H = H.addStab := (addStab_idem _).symm
          _ ⊆ (n • s + H).addStab := subset_addStab_add_right hns
    have key := ih (s + H) hsH
    rw [hstab, hnsH, add_assoc, hHH] at key
    -- Kneser for `n • s` and `s`
    have hk := add_kneser (n • s) s
    rw [← succ_nsmul] at hk
    rw [← hHdef] at hk
    -- combine
    have hsub : (n - 1) * #H + #H = n * #H := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    have hexp : (n + 1) * #(s + H) = n * #(s + H) + #(s + H) := by ring
    simp only [Nat.add_sub_cancel]
    omega

/-- In a finite abelian group `G`, if `s` contains `0`, generates `G` and `2 |G| ≤ h |s|`, then
`h • s = G`. -/
lemma nsmul_eq_univ [Fintype G] {s : Finset G} (h0 : (0 : G) ∈ s)
    (hgen : AddSubgroup.closure (s : Set G) = ⊤) {h : ℕ} (hh : 1 ≤ h)
    (hcard : 2 * Fintype.card G ≤ h * #s) : h • s = univ := by
  by_contra hne
  have hs : s.Nonempty := ⟨0, h0⟩
  set T := h • s with hTdef
  have hT : T.Nonempty := hs.nsmul
  set H := T.addStab with hHdef
  have hH0 : (0 : G) ∈ H := hT.zero_mem_addStab
  have hHstab : (H : Set G) = AddAction.stabilizer G (T : Set G) := coe_addStab hT
  have mem_H : ∀ {k : G}, k ∈ H ↔ k ∈ AddAction.stabilizer G (T : Set G) := by
    intro k; rw [← Finset.mem_coe, hHstab, SetLike.mem_coe]
  -- `T` is a union of `H`-cosets that misses a coset, so `|T| + |H| ≤ |G|`
  obtain ⟨y, hy⟩ : ∃ y, y ∉ T := by
    by_contra hall
    exact hne (eq_univ_of_forall fun x ↦ by by_contra hx; exact hall ⟨x, hx⟩)
  have hdisj : Disjoint T (y +ᵥ H) := by
    rw [Finset.disjoint_left]
    intro z hzT hzH
    obtain ⟨k, hk, rfl⟩ := Finset.mem_vadd_finset.1 hzH
    have hnk : -k ∈ AddAction.stabilizer G (T : Set G) := neg_mem (mem_H.1 hk)
    have : -k +ᵥ (y +ᵥ k) ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hnk]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 hzT)
    apply hy
    have e : -k +ᵥ (y +ᵥ k) = y := by simp [vadd_eq_add]
    rw [e] at this
    exact Finset.mem_coe.1 this
  have hTH : #T + #H ≤ Fintype.card G := by
    rw [← card_vadd_finset y H, ← card_union_of_disjoint hdisj]
    exact card_le_univ _
  -- `s + H` is a union of at least two `H`-cosets
  have hsub : s ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨x, hx, 0, hH0, add_zero x⟩
  have hHsub : H ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨0, h0, x, hx, zero_add x⟩
  have hdvd : #H ∣ #(s + H) := card_addStab_dvd_card_add_addStab s T
  have hHpos : 0 < #H := card_pos.2 ⟨0, hH0⟩
  have hne2 : #(s + H) ≠ #H := by
    intro heq
    have hsH : s + H = H := (eq_of_subset_of_card_le hHsub heq.le).symm
    have hsH' : (s : Set G) ⊆ AddAction.stabilizer G (T : Set G) := by
      intro x hx
      exact mem_H.1 (hsH ▸ hsub (Finset.mem_coe.1 hx))
    have htop : AddAction.stabilizer G (T : Set G) = ⊤ :=
      eq_top_iff.2 (hgen ▸ (AddSubgroup.closure_le _).2 hsH')
    apply hne
    apply eq_univ_of_forall
    intro g
    obtain ⟨t, ht⟩ := hT
    have hg : g - t ∈ AddAction.stabilizer G (T : Set G) := htop ▸ AddSubgroup.mem_top _
    have : (g - t) +ᵥ t ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hg]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 ht)
    simpa [vadd_eq_add] using this
  have h2H : 2 * #H ≤ #(s + H) := by
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c ≠ 1 := by rintro rfl; exact hne2 (by rw [hc, mul_one])
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hne' : (s + H).Nonempty := hs.add ⟨0, hH0⟩
      rw [mul_zero, card_eq_zero] at hc
      exact hne'.ne_empty hc
    rw [hc]
    have : 2 ≤ c := by omega
    nlinarith
  have hsle : #s ≤ #(s + H) := card_le_card hsub
  have hK := kneser_nsmul hh s hs
  rw [← hTdef, ← hHdef] at hK
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hK
  have h3 : k * (2 * #H) ≤ k * #(s + H) := Nat.mul_le_mul_left k h2H
  have h4 : (k + 1) * #s ≤ (k + 1) * #(s + H) := Nat.mul_le_mul_left _ hsle
  nlinarith

/-- An element of `h • (A.image f)` is the image of a sum of `h` elements of `A`. -/
lemma exists_multiset_of_mem_nsmul_image {f : ℕ →+ G} {A : Finset ℕ} :
    ∀ {h : ℕ} {z : G}, z ∈ h • A.image f →
      ∃ M : Multiset ℕ, M.card = h ∧ (∀ a ∈ M, a ∈ A) ∧ f M.sum = z := by
  intro h
  induction h with
  | zero =>
    intro z hz
    rw [zero_nsmul, Finset.mem_zero] at hz
    exact ⟨0, by simp, by simp, by simp [hz]⟩
  | succ n ih =>
    intro z hz
    rw [succ_nsmul, Finset.mem_add] at hz
    obtain ⟨x, hx, w, hw, rfl⟩ := hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨M, hMc, hMA, hMs⟩ := ih hx
    refine ⟨a ::ₘ M, by simp [hMc], ?_, ?_⟩
    · intro b hb
      rcases Multiset.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hMA b hb
    · rw [Multiset.sum_cons, map_add, hMs, add_comm]

/-- If every residue mod `ℓ` is a sum of `h` elements of `A ⊆ [0, ℓ]` and `0, ℓ ∈ A`, then every
`x` with `h ℓ ≤ x` and `x + h ℓ ≤ m ℓ` is a sum of exactly `m` elements of `A`. -/
lemma exists_multiset_of_nsmul_eq_univ {A : Finset ℕ} {ℓ h m x : ℕ} [NeZero ℓ]
    (hA0 : 0 ∈ A) (hAℓ : ℓ ∈ A) (hle : ∀ a ∈ A, a ≤ ℓ)
    (huniv : h • A.image (Nat.castAddMonoidHom (ZMod ℓ)) = univ)
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ A) ∧ M.sum = x := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  obtain ⟨M₀, hc, hA, hs⟩ := exists_multiset_of_mem_nsmul_image
    (huniv ▸ Finset.mem_univ (x : ZMod ℓ))
  simp only [Nat.coe_castAddMonoidHom] at hs
  have hsum : M₀.sum ≤ h * ℓ := by
    rw [← hc]
    exact Multiset.sum_le_card_nsmul _ _ fun a ha ↦ hle a (hA a ha)
  have hmod : M₀.sum ≡ x [MOD ℓ] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hs
  obtain ⟨j, hj⟩ : ℓ ∣ x - M₀.sum := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  have hjm : h + j ≤ m := by
    have : j * ℓ ≤ x := by rw [mul_comm]; omega
    by_contra hcon
    have : m * ℓ < (h + j) * ℓ := Nat.mul_lt_mul_of_pos_right (by omega) hℓ
    nlinarith
  refine ⟨M₀ + Multiset.replicate j ℓ + Multiset.replicate (m - (h + j)) 0, ?_, ?_, ?_⟩
  · simp [hc]; omega
  · intro a ha
    simp only [Multiset.mem_add, Multiset.mem_replicate] at ha
    rcases ha with (ha | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact hA a ha
    · exact hAℓ
    · exact hA0
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_zero, add_zero]
    rw [mul_comm j ℓ, ← hj]
    omega

end Erdos338Proof
/-!
# Sums of a bounded number of elements of a set of positive density

If `E ⊆ ℕ` contains `0`, its elements generate `ℤ`, and `E` has lower density at least `γ > 0`
(in the form `γ b ≤ |E ∩ [0, b)|` for all large `b`), then every large integer is a sum of exactly
`K` elements of `E`, where `K` depends only on `γ` (`cover`). The proof applies
`Erdos338Proof.nsmul_eq_univ` to `E ∩ [0, ℓ]` in `ZMod ℓ` for suitable `ℓ ∈ E`.
-/

open Finset
open scoped Pointwise

namespace Erdos338Proof

open Classical in
/-- `cnt S b` is the number of elements of `S` below `b`. -/
noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := #((range b).filter (· ∈ S))

lemma cnt_le_of_subset {S : Set ℕ} {b c : ℕ} (h : ∀ x ∈ S, x < b → x < c) : cnt S b ≤ c := by
  classical
  unfold cnt
  calc #((range b).filter (· ∈ S)) ≤ #(range c) := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_range] at hx
        exact mem_range.2 (h x hx.2 hx.1)
    _ = c := card_range c

/-- One dense step: for a large `ℓ ∈ E`, every `x` with `h ℓ ≤ x` and `x + h ℓ ≤ m ℓ` is a sum
of `m` elements of `E`. -/
lemma dense_step_window {γ : ℝ} (hγ : 0 < γ) {h : ℕ} (hh : (4 / γ : ℝ) < h) {E : Set ℕ}
    {F : Finset ℕ} (hFE : (F : Set ℕ) ⊆ E)
    (h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) (hE0 : 0 ∈ E) {ℓ : ℕ} (hℓE : ℓ ∈ E) (hN : γ * ℓ ≤ cnt E ℓ) (hℓF : F.sup id ≤ ℓ) (hℓγ : (2 / γ : ℝ) ≤ ℓ) {m x : ℕ}
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  classical
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < 2 / γ := by positivity
    exact_mod_cast this.trans_le hℓγ
  have : NeZero ℓ := ⟨hℓpos.ne'⟩
  set A := (range (ℓ + 1)).filter (· ∈ E) with hA
  have hA0 : 0 ∈ A := by simp [hA, hE0]
  have hAℓ : ℓ ∈ A := by simp [hA, hℓE]
  have hle : ∀ a ∈ A, a ≤ ℓ := by
    intro a ha
    simp only [hA, mem_filter, mem_range] at ha
    omega
  set f := Nat.castAddMonoidHom (ZMod ℓ)
  set S := A.image f with hS
  -- `S` is large
  have hAcnt : γ * ℓ ≤ #A := by
    have h1 := hN
    have h2 : cnt E ℓ ≤ #A := by
      unfold cnt
      apply card_le_card
      intro a ha
      simp only [mem_filter, mem_range] at ha
      rw [hA]
      exact mem_filter.2 ⟨mem_range.2 (by omega), ha.2⟩
    exact h1.trans (by exact_mod_cast h2)
  have hScard : #A ≤ #S + 1 := by
    have hinj : Set.InjOn f (A.erase ℓ : Set ℕ) := by
      intro a ha b hb hab
      simp only [coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
      have ha' : a < ℓ := lt_of_le_of_ne (hle a ha.1) ha.2
      have hb' : b < ℓ := lt_of_le_of_ne (hle b hb.1) hb.2
      have := congrArg ZMod.val hab
      simp only [f, Nat.coe_castAddMonoidHom, ZMod.val_natCast] at this
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
    have h1 : #(A.erase ℓ) ≤ #S := by
      rw [← card_image_of_injOn hinj]
      exact card_le_card (image_subset_image (erase_subset ℓ A))
    have h2 := card_erase_add_one hAℓ
    omega
  have hcard : 2 * Fintype.card (ZMod ℓ) ≤ h * #S := by
    rw [ZMod.card]
    have hS' : (γ * ℓ - 1 : ℝ) ≤ #S := by
      have : (#A : ℝ) ≤ #S + 1 := by exact_mod_cast hScard
      linarith
    have hpos : (0 : ℝ) ≤ γ * ℓ - 1 := by
      have : γ * (2 / γ) ≤ γ * ℓ := mul_le_mul_of_nonneg_left hℓγ hγ.le
      rw [mul_div_cancel₀ _ hγ.ne'] at this
      linarith
    have key : (4 / γ) * (γ * ℓ - 1) ≤ (h : ℝ) * #S :=
      mul_le_mul hh.le hS' hpos (by positivity)
    have e : (4 / γ) * (γ * ℓ - 1) = 4 * ℓ - 4 / γ := by field_simp
    have h4 : (4 / γ : ℝ) ≤ 2 * ℓ := by
      have : (4 / γ : ℝ) = 2 * (2 / γ) := by ring
      linarith
    have : (2 * ℓ : ℝ) ≤ h * #S := by linarith
    exact_mod_cast this
  -- `S` generates `ZMod ℓ`
  have hgen : AddSubgroup.closure (S : Set (ZMod ℓ)) = ⊤ := by
    set φ : ℤ →ₗ[ℤ] ZMod ℓ := (Int.castAddHom (ZMod ℓ)).toIntLinearMap
    have hmap : (1 : ZMod ℓ) ∈ Submodule.span ℤ (S : Set (ZMod ℓ)) := by
      have h2 : φ 1 ∈ Submodule.span ℤ (φ '' ((Nat.cast : ℕ → ℤ) '' F)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have e1 : φ 1 = 1 := by simp [φ]
      rw [e1] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, ?_, by simp [φ, f]⟩)
      simp only [hA, mem_filter, mem_range]
      refine ⟨?_, hFE hn⟩
      have : n ≤ F.sup id := Finset.le_sup (f := id) hn
      omega
    replace hmap : (1 : ZMod ℓ) ∈ (Submodule.span ℤ (S : Set (ZMod ℓ))).toAddSubgroup := hmap
    rw [Submodule.span_int_eq_addSubgroupClosure] at hmap
    rw [eq_top_iff]
    intro z _
    have : (z.val : ℕ) • (1 : ZMod ℓ) ∈ AddSubgroup.closure (S : Set (ZMod ℓ)) :=
      AddSubgroup.nsmul_mem _ hmap _
    simpa using this
  have h0S : (0 : ZMod ℓ) ∈ S := Finset.mem_image.2 ⟨0, hA0, by simp [f]⟩
  have hh1 : 1 ≤ h := by
    have : (0 : ℝ) < h := lt_of_le_of_lt (by positivity) hh
    exact_mod_cast this
  have huniv := nsmul_eq_univ h0S hgen hh1 hcard
  obtain ⟨M, hMc, hMA, hMs⟩ := exists_multiset_of_nsmul_eq_univ hA0 hAℓ hle huniv hx1 hx2
  refine ⟨M, hMc, fun a ha ↦ ?_, hMs⟩
  have := hMA a ha
  simp only [hA, mem_filter] at this
  exact this.2

/-- A set `E` with `γ b ≤ |E ∩ [0, b)|` for all large `b` has an element in `(y, C y]` for all
large `y`, once `2 / γ ≤ C`. -/
lemma exists_mem_Ioc {γ : ℝ} (hγ : 0 < γ) {C : ℕ} (hC : (2 / γ : ℝ) ≤ C) {E : Set ℕ} {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) {y : ℕ} (hyN : N ≤ y) (hy2 : 2 ≤ y) :
    ∃ ℓ ∈ E, y < ℓ ∧ ℓ ≤ C * y := by
  by_contra hcon
  push Not at hcon
  have hC1 : 1 ≤ C := by
    have : (0 : ℝ) < C := lt_of_lt_of_le (by positivity) hC
    exact_mod_cast this
  have hle : cnt E (C * y + 1) ≤ y + 1 := by
    apply cnt_le_of_subset
    intro x hx hxb
    by_contra hxy
    exact absurd (hcon x hx (by omega)) (by omega)
  have hb : N ≤ C * y + 1 := by nlinarith
  have h1 := hN _ hb
  have h2 : (cnt E (C * y + 1) : ℝ) ≤ y + 1 := by exact_mod_cast hle
  have h3 : (2 : ℝ) ≤ γ * C := by
    have := mul_le_mul_of_nonneg_left hC hγ.le
    rwa [mul_div_cancel₀ _ hγ.ne'] at this
  have hy : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  push_cast at h1
  nlinarith

/-- **Covering**: for `γ > 0` there is `K` such that every `E ⊆ ℕ` containing `0`, whose elements
generate `ℤ`, and with `γ b ≤ |E ∩ [0, b)|` for all large `b`, contains every large integer as a
sum of exactly `K` elements. -/
theorem cover {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, (2 / γ : ℝ) < K ∧ ∀ E : Set ℕ, 0 ∈ E →
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ E ∧ (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) →
    (∃ N, ∀ b ≥ N, γ * b ≤ cnt E b) →
    ∃ N', ∀ x ≥ N', ∃ M : Multiset ℕ, M.card = K ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  set h : ℕ := ⌈4 / γ⌉₊ + 1 with hhdef
  set C : ℕ := ⌈2 / γ⌉₊ + 1 with hCdef
  have hh : (4 / γ : ℝ) < h := by
    rw [hhdef]; push_cast; linarith [Nat.le_ceil (4 / γ)]
  have hC : (2 / γ : ℝ) ≤ C := by
    rw [hCdef]; push_cast; linarith [Nat.le_ceil (2 / γ)]
  have hh1 : 1 ≤ h := by omega
  have hC1 : 1 ≤ C := by omega
  refine ⟨h * (C + 1), ?_, ?_⟩
  · have : (h : ℝ) ≤ h * (C + 1) := by
      have : (1 : ℝ) ≤ C + 1 := by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
      nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    have h42 : (2 / γ : ℝ) < 4 / γ := by
      apply div_lt_div_of_pos_right (by norm_num) hγ
    push_cast
    linarith
  rintro E hE0 ⟨F, hFE, h1⟩ ⟨N, hN⟩
  set L : ℕ := N + F.sup id + ⌈2 / γ⌉₊ + 2 with hL
  refine ⟨h * C * (L + 1), fun x hx ↦ ?_⟩
  have hhC : 0 < h * C := Nat.mul_pos (by omega) (by omega)
  set y := x / (h * C) with hy
  have hyL : L + 1 ≤ y := by
    rw [hy]
    exact (Nat.le_div_iff_mul_le hhC).2 (by rw [mul_comm]; exact hx)
  obtain ⟨ℓ, hℓE, hyℓ, hℓy⟩ := exists_mem_Ioc hγ hC hN (y := y) (by omega) (by omega)
  have hℓγ : (2 / γ : ℝ) ≤ ℓ := by
    have : ⌈2 / γ⌉₊ ≤ ℓ := by omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  apply dense_step_window hγ hh hFE h1 hE0 hℓE (hN ℓ (by omega)) (by omega) hℓγ
  · -- `h ℓ ≤ h C y ≤ x`
    calc h * ℓ ≤ h * (C * y) := Nat.mul_le_mul_left h hℓy
      _ = y * (h * C) := by ring
      _ ≤ x := Nat.div_mul_le_self x (h * C)
  · -- `x < h C (y + 1) ≤ h C ℓ`
    have hx' : x < (y + 1) * (h * C) := by rw [hy, mul_comm]; exact Nat.lt_mul_div_succ x hhC
    have : (y + 1) * (h * C) ≤ ℓ * (h * C) := Nat.mul_le_mul_right _ hyℓ
    nlinarith

end Erdos338Proof
/-!
# Bounded sums of a set of positive density

For `γ > 0` there is `K` such that every `M ⊆ ℕ` with `γ b ≤ |M ∩ [0, b)|` for all large `b` has
`d ≤ K` and `b₀` such that every `K b₀ + d x` with `x` large is a sum of exactly `K` elements of
`M` (`usl`). Here `b₀` is any element of `M` and `d` is the greatest common divisor of the
differences `x - b₀` with `x ∈ M`, `x ≥ b₀`; the set `E = {y | b₀ + d y ∈ M}` then satisfies the
hypotheses of `cover`.
-/

open Finset

namespace Erdos338Proof

theorem usl {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, ∀ M : Set ℕ, (∃ N, ∀ b ≥ N, γ * b ≤ cnt M b) →
    ∃ d b₀ N', 1 ≤ d ∧ d ≤ K ∧ ∀ x ≥ N', ∃ Ms : Multiset ℕ, Multiset.card Ms = K ∧
      (∀ a ∈ Ms, a ∈ M) ∧ Ms.sum = K * b₀ + d * x := by
  classical
  obtain ⟨K, hK, hcov⟩ := cover (half_pos hγ)
  have hγK : 4 < K * γ := by
    have e : (2 / (γ / 2) : ℝ) = 4 / γ := by field_simp; norm_num
    rw [e, div_lt_iff₀ hγ] at hK
    exact hK
  refine ⟨K, fun M ⟨N, hN⟩ ↦ ?_⟩
  -- `M` is infinite
  have hlarge : ∀ y, ∃ x ∈ M, y ≤ x := by
    intro y
    by_contra hcon
    push Not at hcon
    set b := N + ⌈((y : ℝ) + 1) / γ⌉₊ with hb
    have h1 := hN b (by omega)
    have h2 : cnt M b ≤ y := cnt_le_of_subset fun x hx _ ↦ hcon x hx
    have h3 : ((y : ℝ) + 1) / γ ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈((y : ℝ) + 1) / γ⌉₊ ≤ b))
    have h4 : (y : ℝ) + 1 ≤ γ * b := by rwa [div_le_iff₀ hγ, mul_comm] at h3
    have h5 : (cnt M b : ℝ) ≤ y := by exact_mod_cast h2
    linarith
  obtain ⟨b₀, hb₀, -⟩ := hlarge 0
  set D : Set ℕ := {u | b₀ + u ∈ M} with hD
  set I := Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' D) with hI
  have hex : ∃ n : ℕ, 0 < n ∧ (n : ℤ) ∈ I := by
    obtain ⟨x, hx, hxb⟩ := hlarge (b₀ + 1)
    refine ⟨x - b₀, by omega, Submodule.subset_span ⟨x - b₀, ?_, rfl⟩⟩
    show b₀ + (x - b₀) ∈ M
    rwa [show b₀ + (x - b₀) = x by omega]
  set d := Nat.find hex with hddef
  have hd : 0 < d ∧ (d : ℤ) ∈ I := Nat.find_spec hex
  -- `d` divides every element of `D`
  have hdvd : ∀ u ∈ D, d ∣ u := by
    intro u hu
    have hu' : (u : ℤ) ∈ I := Submodule.subset_span ⟨u, hu, rfl⟩
    have hmod : ((u % d : ℕ) : ℤ) ∈ I := by
      have e : ((u % d : ℕ) : ℤ) = (u : ℤ) - ((u / d : ℕ) : ℤ) * (d : ℤ) := by
        have := Nat.mod_add_div u d
        push_cast
        linarith [this]
      rw [e]
      exact I.sub_mem hu' (I.smul_mem _ hd.2)
    by_contra hnd
    have hpos : 0 < u % d := Nat.pos_of_ne_zero fun h ↦ hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt u hd.1) ⟨hpos, hmod⟩
  have hdecomp : ∀ x ∈ M, b₀ ≤ x → ∃ q, x = b₀ + d * q ∧ q ∈ {y | b₀ + d * y ∈ M} := by
    intro x hx hxb
    have hu : x - b₀ ∈ D := by
      show b₀ + (x - b₀) ∈ M
      rwa [show b₀ + (x - b₀) = x by omega]
    obtain ⟨q, hq⟩ := hdvd _ hu
    refine ⟨q, by omega, ?_⟩
    show b₀ + d * q ∈ M
    rwa [← hq, show b₀ + (x - b₀) = x by omega]
  set E : Set ℕ := {y | b₀ + d * y ∈ M} with hE
  have hE0 : 0 ∈ E := by simpa [hE] using hb₀
  -- a finite generating subset of `E`
  obtain ⟨T, hTD, hdT⟩ := Submodule.mem_span_finite_of_mem_span hd.2
  set F : Finset ℕ := T.image fun z ↦ z.toNat / d with hF
  have hFE : (F : Set ℕ) ⊆ E := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
    obtain ⟨u, hu, rfl⟩ := hTD hz
    show b₀ + d * ((u : ℤ).toNat / d) ∈ M
    rw [Int.toNat_natCast, Nat.mul_div_cancel' (hdvd u hu)]
    exact hu
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F) := by
    set f : ℤ →ₗ[ℤ] ℤ := LinearMap.mulLeft ℤ (d : ℤ) with hf
    have hT : (T : Set ℤ) ⊆ f '' ((Nat.cast : ℕ → ℤ) '' F) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hTD hz
      refine ⟨((u / d : ℕ) : ℤ), ⟨u / d, mem_image.2 ⟨u, hz, by simp⟩, rfl⟩, ?_⟩
      simp only [hf, LinearMap.mulLeft_apply]
      exact_mod_cast Nat.mul_div_cancel' (hdvd u hu)
    have hmem : (d : ℤ) ∈ Submodule.map f (Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono hT hdT
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.1 hmem
    have hy1 : y = 1 := by
      simp only [hf, LinearMap.mulLeft_apply] at hfy
      have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.1.ne'
      exact mul_left_cancel₀ hd0 (hfy.trans (mul_one _).symm)
    rwa [hy1] at hy
  -- counting `M` through `E`
  have hcntM : ∀ b, cnt M b ≤ b₀ + cnt E b := by
    intro b
    unfold cnt
    have hsub : (range b).filter (· ∈ M) ⊆
        range b₀ ∪ ((range b).filter (· ∈ E)).image fun y ↦ b₀ + d * y := by
      intro x hx
      rw [mem_filter, mem_range] at hx
      rw [mem_union, mem_range, mem_image]
      by_cases hxb : x < b₀
      · exact Or.inl hxb
      · obtain ⟨q, rfl, hq⟩ := hdecomp x hx.2 (by omega)
        have : q ≤ d * q := Nat.le_mul_of_pos_left q hd.1
        exact Or.inr ⟨q, mem_filter.2 ⟨mem_range.2 (by omega), hq⟩, rfl⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := by rw [card_range]; exact Nat.add_le_add_left card_image_le _
  have hcntM2 : ∀ b, cnt M b ≤ b₀ + (b / d + 1) := by
    intro b
    unfold cnt
    have hsub : (range b).filter (· ∈ M) ⊆
        range b₀ ∪ (range (b / d + 1)).image fun y ↦ b₀ + d * y := by
      intro x hx
      rw [mem_filter, mem_range] at hx
      rw [mem_union, mem_range, mem_image]
      by_cases hxb : x < b₀
      · exact Or.inl hxb
      · obtain ⟨q, rfl, -⟩ := hdecomp x hx.2 (by omega)
        refine Or.inr ⟨q, mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩
        rw [Nat.le_div_iff_mul_le hd.1, mul_comm]
        omega
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add (card_range _).le (card_image_le.trans (card_range _).le)
  -- `d ≤ K`
  have hdK : d ≤ K := by
    by_contra hdK
    push Not at hdK
    set b := N + ⌈(2 * (b₀ : ℝ) + 2) / γ⌉₊ with hb
    have h1 := hN b (by omega)
    have h2 := hcntM2 b
    set q := b / d with hq
    have h3 : q * d ≤ b := Nat.div_mul_le_self b d
    have h4 : q * K ≤ b := (Nat.mul_le_mul_left q hdK.le).trans h3
    have h5 : ((2 * (b₀ : ℝ) + 2) / γ) ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(2 * (b₀ : ℝ) + 2) / γ⌉₊ ≤ b))
    have h6 : 2 * (b₀ : ℝ) + 2 ≤ γ * b := by rw [div_le_iff₀ hγ] at h5; linarith
    have h2' : (cnt M b : ℝ) ≤ b₀ + (q + 1) := by exact_mod_cast h2
    have h4' : (q : ℝ) * K ≤ b := by exact_mod_cast h4
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have h7 : 4 * (q : ℝ) ≤ γ * b := by
      have := mul_le_mul_of_nonneg_left h4' hγ.le
      nlinarith
    linarith
  -- density of `E`
  have hdens : ∃ N₁, ∀ b ≥ N₁, γ / 2 * b ≤ cnt E b := by
    refine ⟨N + ⌈2 * (b₀ : ℝ) / γ⌉₊, fun b hb ↦ ?_⟩
    have h1 := hN b (by omega)
    have h2 : (cnt M b : ℝ) ≤ b₀ + cnt E b := by exact_mod_cast hcntM b
    have h3 : 2 * (b₀ : ℝ) / γ ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 * (b₀ : ℝ) / γ⌉₊ ≤ b))
    have h4 : 2 * (b₀ : ℝ) ≤ γ * b := by rw [div_le_iff₀ hγ] at h3; linarith
    linarith
  obtain ⟨N', hN'⟩ := hcov E hE0 ⟨F, hFE, h1⟩ hdens
  refine ⟨d, b₀, N', hd.1, hdK, fun x hx ↦ ?_⟩
  obtain ⟨Me, hMe1, hMe2, hMe3⟩ := hN' x hx
  refine ⟨Me.map fun y ↦ b₀ + d * y, by simp [hMe1], ?_, ?_⟩
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 ha
    exact hMe2 y hy
  · rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, Multiset.sum_map_mul_left,
      Multiset.map_id', hMe3, hMe1, smul_eq_mul]

end Erdos338Proof
/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
