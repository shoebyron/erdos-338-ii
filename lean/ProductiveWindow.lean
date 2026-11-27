import SingleSetCovering
import InfiniteLevels

/-! Finite cyclic Kneser at a single productive window. The normalization
uses the integer span as in Veljjanoski's Shift.lean, cited in SingleSetCovering.
A single modulus is fixed before the choice of window. -/

namespace Erdos338.Bridge

open Filter Finset
open scoped BigOperators Pointwise Classical

private theorem normalize_set {C : Set ℕ} (hp : ∃ n ∈ C, 0 < n) :
    ∃ d : ℕ, 0 < d ∧ (∀ x ∈ C, d ∣ x) ∧ ∃ F : Finset ℕ,
      ((F : Set ℕ) ⊆ {y | d*y ∈ C}) ∧ (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F) := by
  classical
  let I := Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' C)
  have hex : ∃ n : ℕ, 0 < n ∧ (n : ℤ) ∈ I := by
    obtain ⟨n, hn, hpos⟩ := hp
    exact ⟨n, hpos, Submodule.subset_span ⟨n, hn, rfl⟩⟩
  let d := Nat.find hex
  have hd : 0 < d ∧ (d : ℤ) ∈ I := Nat.find_spec hex
  have hdvd : ∀ x ∈ C, d ∣ x := by
    intro x hx
    have hx' : (x : ℤ) ∈ I := Submodule.subset_span ⟨x, hx, rfl⟩
    have hmod : ((x % d : ℕ) : ℤ) ∈ I := by
      have e : ((x % d : ℕ) : ℤ) = (x : ℤ) - ((x / d : ℕ) : ℤ) * (d : ℤ) := by
        have := Nat.mod_add_div x d
        push_cast
        linarith [this]
      rw [e]
      exact I.sub_mem hx' (I.smul_mem _ hd.2)
    by_contra hnd
    have hpos : 0 < x % d := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt x hd.1) ⟨hpos, hmod⟩
  obtain ⟨T, hTC, hdT⟩ := Submodule.mem_span_finite_of_mem_span hd.2
  let F := T.image fun z => z.toNat / d
  refine ⟨d, hd.1, hdvd, F, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, rfl⟩ := hTC hz
    change d * ((u : ℤ).toNat / d) ∈ C
    rwa [Int.toNat_natCast, Nat.mul_div_cancel' (hdvd u hu)]
  · let f : ℤ →ₗ[ℤ] ℤ := LinearMap.mulLeft ℤ (d : ℤ)
    have hT : (T : Set ℤ) ⊆ f '' ((Nat.cast : ℕ → ℤ) '' F) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hTC hz
      refine ⟨((u / d : ℕ) : ℤ), ⟨u / d, Finset.mem_image.mpr ⟨u, hz, by simp⟩, rfl⟩, ?_⟩
      simp only [f, LinearMap.mulLeft_apply]
      exact_mod_cast Nat.mul_div_cancel' (hdvd u hu)
    have hmem : (d : ℤ) ∈ Submodule.map f (Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono hT hdT
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.mp hmem
    have hy1 : y = 1 := by
      simp only [f, LinearMap.mulLeft_apply] at hfy
      have hd0 : (d : ℤ) ≠ 0 := (by exact_mod_cast hd.1.ne')
      exact mul_left_cancel₀ hd0 (hfy.trans (mul_one _).symm)
    rwa [hy1] at hy

private theorem scaled_multiset_mem {d : ℕ} {C : Set ℕ} (M : Multiset ℕ)
    (hM : ∀ x ∈ M, d*x ∈ C) : d*M.sum ∈ M.card • C := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    rw [Multiset.sum_cons, Nat.mul_add, Multiset.card_cons, succ_nsmul]
    rw [Nat.add_comm]
    exact Set.add_mem_add (ih (fun x hx => hM x (Multiset.mem_cons_of_mem hx)))
      (hM a (Multiset.mem_cons_self a M))

/-- At every productive window, one of its elements serves both as a padding
summand and as the modulus in a finite cyclic Kneser argument. The gcd d
is chosen once for C and positive original targets are multiples of d. -/
theorem localCoverAtProductiveWindows (C : Set ℕ) (h0 : 0 ∈ C) (L : ℕ) (hL : 0 < L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ X : ℕ in atTop, 6*X ≤ L*windowCount C (2*X) →
      ∃ ℓ ∈ C, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L*ℓ ∧ d ≤ L ∧
        ∀ u k : ℕ, d ∣ u → (4*(L+1))*ℓ ≤ u → u + (4*(L+1))*ℓ ≤ k*ℓ → u ∈ k • C := by
  classical
  by_cases hp : ∃ x ∈ C, 0 < x
  case neg =>
    refine ⟨1, Nat.one_pos, ?_⟩
    filter_upwards [eventually_gt_atTop L] with X hX
    intro hm
    have hsub : (Finset.Icc 0 (2*X)).filter (· ∈ C) ⊆ {0} := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      exact Finset.mem_singleton.mpr (by by_contra hn; exact hp ⟨x, h, Nat.pos_of_ne_zero hn⟩)
    have hw : windowCount C (2*X) ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    have := Nat.mul_le_mul_left L hw
    omega
  obtain ⟨d, hd, hdvd, F, hFE, hF⟩ := normalize_set hp
  let E : Set ℕ := {y | d*y ∈ C}
  have he0 : 0 ∈ E := by simpa [E] using h0
  let c := 4*(L+1)
  let T := F.sup id + 2*L + 1
  refine ⟨d, hd, ?_⟩
  filter_upwards [eventually_gt_atTop (L*(d*T) + L)] with X hX
  intro hm
  let V := (Finset.Icc 0 (2*X)).filter (· ∈ C)
  have hV : 6*X ≤ L*V.card := hm
  have hne : V.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩, h0⟩⟩
  let ℓ := V.max' hne
  have hℓV : ℓ ∈ V := Finset.max'_mem _ _
  have hℓC : ℓ ∈ C := (Finset.mem_filter.mp hℓV).2
  have hℓX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hℓV).1).2
  have hlarg : X ≤ L*ℓ := by
    have hsub : V ⊆ Finset.range (ℓ+1) := fun x hx => Finset.mem_range.mpr (by
      exact Nat.lt_succ_of_le (Finset.le_max' V x hx))
    have hvle : V.card ≤ ℓ+1 := (Finset.card_le_card hsub).trans (by simp)
    have hh := Nat.mul_le_mul_left L hvle
    rw [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hℓpos : 0 < ℓ := by by_contra! hn; simp [Nat.eq_zero_of_le_zero hn] at hlarg; omega
  let z := ℓ/d
  have hdz : d*z = ℓ := Nat.mul_div_cancel' (hdvd ℓ hℓC)
  have hzT : T ≤ z := by
    by_contra! hz
    have hlt := Nat.mul_lt_mul_of_pos_left hz hd
    have hb := Nat.mul_le_mul_left L hlt.le
    rw [hdz] at hb
    omega
  have hzE : z ∈ E := by simpa [E, hdz] using hℓC
  have hdivinj : Set.InjOn (fun x : ℕ => x/d) (V : Set ℕ) := by
    intro x hx y hy he
    have h1 := Nat.mul_div_cancel' (hdvd x (Finset.mem_filter.mp hx).2)
    have h2 := Nat.mul_div_cancel' (hdvd y (Finset.mem_filter.mp hy).2)
    change x/d = y/d at he
    rw [he] at h1
    exact h1.symm.trans h2
  have hncard : V.card ≤ Erdos338Proof.cnt E z + 1 := by
    let P := (Finset.range z).filter (· ∈ E)
    have hsub : V.image (fun x => x/d) ⊆ insert z P := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      have xle : x/d ≤ z := Nat.div_le_div_right (Finset.le_max' V x hx)
      rcases Nat.eq_or_lt_of_le xle with heq | hlt
      · rw [heq]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr hlt, ?_⟩
        change d*(x/d) ∈ C
        rw [Nat.mul_div_cancel' (hdvd x (Finset.mem_filter.mp hx).2)]
        exact (Finset.mem_filter.mp hx).2
    rw [← Finset.card_image_of_injOn hdivinj]
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hVsmall : V.card ≤ z+1 := by
    apply hncard.trans
    have hc : Erdos338Proof.cnt E z ≤ z := by
      simpa [Erdos338Proof.cnt] using Finset.card_filter_le (Finset.range z) (· ∈ E)
    omega
  have hdL : d ≤ L := by
    by_contra! hgt
    have hzL := Nat.mul_le_mul_right z hgt.le
    have hvc := Nat.mul_le_mul_left L hVsmall
    rw [Nat.mul_add, Nat.mul_one] at hvc
    omega
  have hzle : z ≤ 2*X := (Nat.div_le_self _ _).trans hℓX
  have hcnt : z ≤ L * Erdos338Proof.cnt E z := by
    have hu := Nat.mul_le_mul_left L hncard
    rw [Nat.mul_add, Nat.mul_one] at hu
    omega
  have hg : 0 < 1/(L : ℝ) := by positivity
  have hcg : 4/(1/(L : ℝ)) < (c : ℝ) := by simp [c, Nat.cast_add, Nat.cast_mul]
  have hzBig : 2/(1/(L : ℝ)) ≤ (z : ℝ) := by
    suffices 2 * L ≤ z by simpa using (show (2 : ℝ)*L ≤ z by exact_mod_cast this)
    dsimp [T] at hzT
    omega
  have hratio : (1/(L : ℝ))*z ≤ (Erdos338Proof.cnt E z : ℝ) := by
    rw [one_div, inv_mul_eq_div, div_le_iff₀ (by exact_mod_cast hL), mul_comm]
    exact_mod_cast hcnt
  refine ⟨ℓ, hℓC, hℓpos, hℓX, hlarg, hdL, ?_⟩
  intro u k hdu hl hu
  obtain ⟨v, rfl⟩ := hdu
  change c*ℓ ≤ d*v at hl
  change d*v+c*ℓ ≤ k*ℓ at hu
  have hdc : d*(c*z) = c*ℓ := (Nat.mul_left_comm d c z).trans (congrArg (c*·) hdz)
  have hdk : d*(k*z) = k*ℓ := (Nat.mul_left_comm d k z).trans (congrArg (k*·) hdz)
  have hl' : c*z ≤ v := Nat.le_of_mul_le_mul_left (by rwa [hdc]) hd
  have hu' : v+c*z ≤ k*z := Nat.le_of_mul_le_mul_left (by rwa [Nat.mul_add, hdc, hdk]) hd
  obtain ⟨M, hcard, hM, hsum⟩ := Erdos338Proof.dense_step_window hg hcg hFE hF he0 hzE
    hratio (by dsimp [T] at hzT; omega) hzBig hl' hu'
  have hres := scaled_multiset_mem (d := d) (C := C) M hM
  rwa [hsum, hcard] at hres

#print axioms localCoverAtProductiveWindows

end Erdos338.Bridge
