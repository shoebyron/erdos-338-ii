import Mathlib

open Filter
open scoped Pointwise BigOperators

namespace Erdos338.Bridge

/-- Enough copies both for the covering interval and for the other scale's multiples. -/
def twoScaleCap (L : ℕ) : ℕ := 2*(4*(L+1)) + 4*L^2 + 2*(4*(L+1))*L

private theorem mul_mem_copies {C : Set ℕ} {q : ℕ} (hzero : 0 ∈ C) (hq : q ∈ C)
    (K k : ℕ) (hk : k ≤ K) : k*q ∈ K • C := by
  induction K generalizing k with
  | zero =>
    have : k = 0 := by omega
    simp [this]
  | succ K ih =>
    rw [succ_nsmul]
    cases k with
    | zero =>
      have h := ih 0 (by omega)
      simpa using (Set.add_mem_add h hzero)
    | succ k =>
      simpa [Nat.succ_mul] using (Set.add_mem_add (ih k (by omega)) hq)

private theorem glueAdjacent {A B : Set ℕ} {I J d p q X n : ℕ}
    (hzero : 0 ∈ B) (hq : q ∈ B) (hX : 0 < X)
    (hp : 0 < p) (hposq : 0 < q) (hpX : p ≤ 2*X) (hqX : q ≤ 2*(X+1))
    (hXI : X ≤ I*p) (hXJ : X+1 ≤ J*q) (hd : 0 < d) (hdI : d ≤ I)
    (hdn : d ∣ n) (hsmall : 2*(4*(I+1))*X ≤ n) (hlarge : n < 2*(4*(J+1))*(X+1))
    (hlocal : ∀ u k : ℕ, d ∣ u → 4*(I+1)*p ≤ u →
      u+4*(I+1)*p ≤ k*p → u ∈ k • A) :
    ∃ u ∈ twoScaleCap I • A, ∃ v ∈ twoScaleCap J • B, u+v=n := by
  let lo := 4*(I+1)*p
  let z := n-lo
  let stride := d*q
  let k := (z/stride)*d
  let v := k*q
  let u := lo+z%stride
  have hlo : lo ≤ n := calc
    lo ≤ 4*(I+1)*(2*X) := Nat.mul_le_mul_left _ hpX
    _ = 2*(4*(I+1))*X := by ring
    _ ≤ n := hsmall
  have hv : v = stride*(z/stride) := by dsimp [v,k,stride]; ring
  have hsum : u+v=n := by
    change (lo+z%stride)+v=n
    rw [hv, Nat.add_assoc, Nat.mod_add_div]
    dsimp [z]
    omega
  have hdv : d ∣ v := ⟨(z/stride)*q, by dsimp [v,k]; ring⟩
  have hdu : d ∣ u := by
    have heq : u = n-v := by omega
    rw [heq]
    exact Nat.dvd_sub hdn hdv
  have hstride : stride ≤ 4*I^2*p := calc
    d*q ≤ I*(4*X) := Nat.mul_le_mul hdI (by omega)
    _ ≤ I*(4*(I*p)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hXI)
    _ = 4*I^2*p := by ring
  have hmod : z%stride < stride := Nat.mod_lt _ (Nat.mul_pos hd hposq)
  have hu : u+lo ≤ twoScaleCap I*p := calc
    u+lo ≤ (2*(4*(I+1)) + 4*I^2)*p := by
      dsimp [u, lo]
      rw [Nat.add_mul]
      have he : 2*(4*(I+1))*p = 4*(I+1)*p + 4*(I+1)*p := by ring
      omega
    _ ≤ twoScaleCap I*p := Nat.mul_le_mul_right _ (by unfold twoScaleCap; omega)
  have hk : k ≤ twoScaleCap J := by
    have hs : k*q ≤ (2*(4*(J+1))*J)*q := calc
      k*q ≤ n := by change v ≤ n; omega
      _ ≤ 2*(4*(J+1))*(X+1) := by omega
      _ ≤ 2*(4*(J+1))*(J*q) := Nat.mul_le_mul_left _ hXJ
      _ = (2*(4*(J+1))*J)*q := by ring
    have hh : k ≤ 2*(4*(J+1))*J := Nat.le_of_mul_le_mul_right hs hposq
    unfold twoScaleCap
    omega
  exact ⟨u, hlocal u _ hdu (Nat.le_add_right _ _) hu, v,
    mul_mem_copies hzero hq _ k hk, hsum⟩

/-- The rank attached to a scale can vary arbitrarily. Two neighboring scales together
cover each sufficiently large multiple of one common modulus. -/
theorem twoScaleCover (h : ℕ) (C : ℕ → Set ℕ) (L d : ℕ → ℕ)
    (hd : ∀ i<h, 0<d i) (h0 : ∀ i<h, 0∈C i)
    (windows : ∀ᶠ X : ℕ in atTop, ∃ i<h, ∃ p∈C i,
      0<p ∧ p≤2*X ∧ X≤L i*p ∧ d i≤L i ∧
      ∀ u k : ℕ, d i∣u → 4*(L i+1)*p≤u →
        u+4*(L i+1)*p≤k*p → u∈k • C i) :
    ∃ g : ℕ, 0<g ∧ ∀ᶠ n : ℕ in atTop, g∣n → ∃ i<h, ∃ j<h,
      ∃ u∈twoScaleCap (L i) • C i, ∃ v∈twoScaleCap (L j) • C j, u+v=n := by
  classical
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 windows
  let B := X₀+1
  have hwin (t : ℕ) := hX₀ (B+t) (by dsimp [B]; omega)
  choose idx hi p hp hpPos hpX hXp hdL hcover using hwin
  let g := ∏ i ∈ Finset.range h, d i
  have hg : 0<g := Finset.prod_pos (fun i hi => hd i (Finset.mem_range.mp hi))
  refine ⟨g, hg, eventually_atTop.2 ⟨2*(4*(L (idx 0)+1))*B, ?_⟩⟩
  intro n hn hgn
  let fine := fun t : ℕ => 2*(4*(L (idx t)+1))*(B+t) ≤ n
  have hf : fine 0 := by simpa [fine] using hn
  have hc : ¬fine (n+1) := by
    have hp : 1 ≤ 2*(4*(L (idx (n+1))+1)) := by omega
    have hx := Nat.mul_le_mul_right (B+(n+1)) hp
    simp only [one_mul] at hx
    dsimp [fine]
    omega
  have hstep : ∃ t : ℕ, fine t ∧ ¬fine (t+1) := by
    by_contra hnone
    have every (t : ℕ) : fine t := by
      induction t with
      | zero => exact hf
      | succ t ih =>
        by_contra hh
        exact hnone ⟨t, ih, hh⟩
    exact hc (every _)
  obtain ⟨t,hf,hc⟩ := hstep
  have hdiv : d (idx t) ∣ g := Finset.dvd_prod_of_mem d (Finset.mem_range.mpr (hi t))
  refine ⟨idx t, hi t, idx (t+1), hi (t+1), ?_⟩
  apply glueAdjacent (X := B+t) (d := d (idx t))
    (p := p t) (q := p (t+1)) (h0 _ (hi _)) (hp _)
  · dsimp [B]; omega
  · exact hpPos _
  · exact hpPos _
  · exact hpX _
  · simpa [Nat.add_assoc] using hpX (t+1)
  · exact hXp _
  · simpa [Nat.add_assoc] using hXp (t+1)
  · exact hd _ (hi _)
  · exact hdL _
  · exact hdiv.trans hgn
  · exact hf
  · simpa [fine,Nat.add_assoc] using Nat.lt_of_not_ge hc
  · exact hcover _

#print axioms twoScaleCover

end Erdos338.Bridge
