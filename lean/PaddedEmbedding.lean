import PaddedProgression
import KneserFamily

/-! Embedding two scale-dependent ranks in a common schedule with doubled slot counts. -/
namespace Erdos338.Bridge

open scoped Pointwise BigOperators

private theorem zero_mem_prefix (D : ℕ → Set ℕ) (hD : ∀ k, 0 ∈ D k) (t : ℕ) :
    0 ∈ ∑ k ∈ Finset.range t, D k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    simpa using Set.add_mem_add ih (hD t)

private theorem mem_prefix_of_mem_level (D : ℕ → Set ℕ) (hD : ∀ k, 0 ∈ D k)
    (i t : ℕ) (hi : i < t) {u : ℕ} (hu : u ∈ D i) :
    u ∈ ∑ k ∈ Finset.range t, D k := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [Finset.sum_range_succ]
    by_cases he : i = t
    · subst i
      simpa using Set.add_mem_add (zero_mem_prefix D hD t) hu
    · simpa using Set.add_mem_add (ih (by omega)) (hD t)

theorem paddedSums_eq_double (cap : ℕ → ℕ) (A : Set ℕ) (h m b t : ℕ) :
    let allow := fun l => 2 * cap l
    let D := fun i => cap (paddedL allow h m b i) •
      richSums A (2 * (h-i)) (paddedQ allow h m b i)
    paddedSums allow A h m b t = (∑ i ∈ Finset.range t, D i) + ∑ i ∈ Finset.range t, D i := by
  dsimp only
  induction t with
  | zero => simp [paddedSums]; rfl
  | succ t ih =>
    rw [paddedSums, addCopies_eq_pointwise, ih, Finset.sum_range_succ]
    simp only [paddedB, two_mul, add_nsmul]
    ac_rfl

/-- Each of two ranks can use its full allowance, even when the two ranks coincide. -/
theorem two_mem_paddedSums (cap : ℕ → ℕ) (A : Set ℕ) (h m b i j u v : ℕ)
    (hi : i < h) (hj : j < h)
    (hu : u ∈ cap (paddedL (fun l => 2*cap l) h m b i) •
      richSums A (2*(h-i)) (paddedQ (fun l => 2*cap l) h m b i))
    (hv : v ∈ cap (paddedL (fun l => 2*cap l) h m b j) •
      richSums A (2*(h-j)) (paddedQ (fun l => 2*cap l) h m b j)) :
    u+v ∈ paddedSums (fun l => 2*cap l) A h m b h := by
  let allow := fun l => 2*cap l
  let D := fun i => cap (paddedL allow h m b i) • richSums A (2*(h-i)) (paddedQ allow h m b i)
  have hz (k : ℕ) : 0 ∈ D k := Set.zero_mem_nsmul (Or.inl rfl : 0 ∈ richSums A _ _)
  rw [paddedSums_eq_double]
  exact Set.add_mem_add (mem_prefix_of_mem_level D hz i h hi hu)
    (mem_prefix_of_mem_level D hz j h hj hv)

#print axioms two_mem_paddedSums
end Erdos338.Bridge
