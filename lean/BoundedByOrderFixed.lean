import FiniteModular

/-!
# Conditional deduction for Erdős problem 338(ii)

The final theorem takes `UniformDensityInput` and `UniformProgressionInput` as
arguments. Its conclusion reproduces the `bounded_by_order` statement from
`FormalConjectures.ErdosProblems.«338»` using definitions in a separate namespace.
The project only needs the imports already used for `FiniteModular`.
-/

open scoped BigOperators

namespace Erdos338.Bridge

open Filter

/-- Ordinary additive representations allow repetition. -/
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Multiset ℕ, (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum = n

/-- A finite set of at most `h` distinct elements of `A` with sum `n`. -/
def Rep (A : Set ℕ) (h n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum id = n

def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in atTop, Rep A t n

def restrictedSums (A : Set ℕ) (h : ℕ) : Set ℕ := {n | Rep A h n}

open scoped Classical in
/-- An eventual lower counting bound with integer denominator `m`. -/
def DensityBound (B : Set ℕ) (m : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, N ≤ m * ((Finset.range N).filter (fun n => n ∈ B)).card

/-- Density input from Hegyvári, Hennecart and Plagne (Theorem 4.8 in
Hegyvári's 2017 dissertation). Apply the theorem to `1 + (A ∪ {0})`,
subtract `h` from the restricted sums, and take `1/m` strictly below the
resulting uniform lower density bound. The threshold may depend on `A`. -/
def UniformDensityInput : Prop :=
  ∀ h : ℕ, 0 < h → ∃ m : ℕ, 0 < m ∧
    ∀ A : Set ℕ, HasOrder A h → DensityBound (restrictedSums A h) m

/-- Progression input extracted from the proof of Chen, Yang and Zhao,
arXiv:2611.33191v1, Lemma 4. Equation (2) and the following formula for `K`
allow `α_h = 1/(2m)` as a real number. The length bound `K` precedes `A`.
The modulus, residue and threshold precede the choice of the deleted set. -/
def UniformProgressionInput : Prop :=
  ∀ h m b : ℕ, 0 < h → 0 < m → ∃ K : ℕ,
    ∀ A : Set ℕ, DensityBound (restrictedSums A h) m →
      ∃ g : ℕ, 0 < g ∧ ∃ a : ZMod g, ∃ N₀ : ℕ,
        ∀ F : Finset ℕ, (∀ x ∈ F, x ∈ A) → F.card ≤ b →
          ∀ n : ℕ, N₀ ≤ n → (n : ZMod g) = a → Rep (A \ (F : Set ℕ)) K n

open scoped Classical in
/-- A lower counting bound persists after reduction modulo a positive modulus. -/
theorem block_density_reduction (B : Set ℕ) (m : ℕ)
    (h : ∃ N₀ : ℕ, ∀ N ≥ N₀,
      N ≤ m * ((Finset.range N).filter (fun n => n ∈ B)).card)
    (q : ℕ) [NeZero q] :
    q ≤ m * (Finset.univ.filter (fun v : ZMod q => ∃ n ∈ B, (n : ZMod q) = v)).card := by
  classical
  obtain ⟨N₀, hN₀⟩ := h
  let k := N₀ + 1
  let R := Finset.univ.filter (fun v : ZMod q => ∃ n ∈ B, (n : ZMod q) = v)
  let S := (Finset.range (k * q)).filter (fun n => n ∈ B)
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hk : 0 < k := Nat.succ_pos _
  have hlarge : N₀ ≤ k * q :=
    (Nat.le_succ N₀).trans (Nat.le_mul_of_pos_right k hq)
  have hcount : S.card ≤ ((Finset.range k).product R).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n / q, (n : ZMod q)))
    · intro n hn
      change n ∈ (Finset.range (k * q)).filter (fun j => j ∈ B) at hn
      obtain ⟨hnRange, hnB⟩ := Finset.mem_filter.mp hn
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (Finset.mem_range.mp hnRange))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, n, hnB, rfl⟩
    · intro a _ b _ hab
      have hd : a / q = b / q := congrArg Prod.fst hab
      have hz : (a : ZMod q) = (b : ZMod q) := congrArg Prod.snd hab
      have hr : a % q = b % q := by simpa only [ZMod.val_natCast] using congrArg ZMod.val hz
      calc
        a = a % q + q * (a / q) := (Nat.mod_add_div a q).symm
        _ = b % q + q * (b / q) := by rw [hd, hr]
        _ = b := Nat.mod_add_div b q
  have hupper : S.card ≤ k * R.card := by
    calc
      S.card ≤ ((Finset.range k).product R).card := hcount
      _ = (Finset.range k).card * R.card := Finset.card_product (Finset.range k) R
      _ = k * R.card := by rw [Finset.card_range]
  have hboth : k * q ≤ k * (m * R.card) := calc
    k * q ≤ m * S.card := hN₀ _ hlarge
    _ ≤ m * (k * R.card) := Nat.mul_le_mul_left _ hupper
    _ = k * (m * R.card) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hboth hk

/-- A finite set of distinct members of `A` represents a residue modulo `q`. -/
def ModRep (A : Set ℕ) (q : ℕ) (s : Finset ℕ) (v : ZMod q) : Prop :=
  (∀ x ∈ s, x ∈ A) ∧ ((s.sum id : ℕ) : ZMod q) = v

noncomputable def shortMod (A : Set ℕ) (h q : ℕ) [NeZero q] : Finset (ZMod q) := by
  classical
  exact Finset.univ.filter (fun v => ∃ s : Finset ℕ, s.card ≤ h ∧ ModRep A q s v)

@[simp] theorem mem_shortMod (A : Set ℕ) (h q : ℕ) [NeZero q] (v : ZMod q) :
    v ∈ shortMod A h q ↔ ∃ s : Finset ℕ, s.card ≤ h ∧ ModRep A q s v := by
  classical
  simp [shortMod]

/-- Apply the finite sequence theorem to the union of one witness for each residue.
    Whenever a residue has a short witness, choose one of those witnesses. -/
theorem uniformModularForSet (h m : ℕ) (hm : 0 < m) :
    ∃ b : ℕ, ∀ (A : Set ℕ) (q : ℕ) [NeZero q],
      (∀ v : ZMod q, ∃ s : Finset ℕ, ModRep A q s v) →
      q ≤ m * (shortMod A h q).card →
      ∀ v : ZMod q, ∃ s : Finset ℕ, s.card ≤ b ∧ ModRep A q s v := by
  classical
  obtain ⟨b, hb⟩ := FiniteModular.uniformModularBound h m hm
  refine ⟨b, ?_⟩
  intro A q inst cover dense
  have selectWitness (v : ZMod q) :
      ∃ s : Finset ℕ, ModRep A q s v ∧ (v ∈ shortMod A h q → s.card ≤ h) := by
    by_cases hv : v ∈ shortMod A h q
    · obtain ⟨s, hs, hrep⟩ := (mem_shortMod A h q v).mp hv
      exact ⟨s, hrep, fun _ => hs⟩
    · obtain ⟨s, hrep⟩ := cover v
      exact ⟨s, hrep, fun hmem => (hv hmem).elim⟩
  let w (v : ZMod q) := (selectWitness v).choose
  have wrep (v : ZMod q) : ModRep A q (w v) v :=
    (selectWitness v).choose_spec.1
  have wshort (v : ZMod q) : v ∈ shortMod A h q → (w v).card ≤ h :=
    (selectWitness v).choose_spec.2
  let U : Finset ℕ := Finset.univ.biUnion w
  have wsub (v : ZMod q) : w v ⊆ U :=
    fun _ hx => Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hx⟩
  have Usub (x : ℕ) (hx : x ∈ U) : x ∈ A := by
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hx
    exact (wrep v).1 x hv
  let n := Fintype.card ↥U
  let e : ↥U ≃ Fin n := Fintype.equivFin ↥U
  let value : Fin n ↪ ℕ :=
    ⟨fun i => (e.symm i).val,
     fun _ _ hi => e.symm.injective (Subtype.ext hi)⟩
  let a (i : Fin n) : ZMod q := (value i : ℕ)
  have encode (s : Finset ℕ) (hs : s ⊆ U) :
      ∃ t : Finset (Fin n), t.card = s.card ∧ t.sum a = ((s.sum id : ℕ) : ZMod q) := by
    let f : ↥s ↪ Fin n :=
      ⟨fun x => e ⟨x.val, hs x.property⟩,
       fun _ _ he => Subtype.ext (congrArg (fun x : ↥U => x.val) (e.injective he))⟩
    refine ⟨s.attach.map f, by simp, ?_⟩
    rw [Finset.sum_map, Nat.cast_sum]
    change (∑ x ∈ s.attach, (((e.symm (e ⟨x.val, hs x.property⟩)).val : ℕ) : ZMod q)) =
      ∑ x ∈ s, (x : ZMod q)
    simpa only [Equiv.symm_apply_apply] using
      Finset.sum_attach s (fun x : ℕ => (x : ZMod q))
  have windex (v : ZMod q) :
      ∃ t : Finset (Fin n), t.card = (w v).card ∧ t.sum a = v := by
    obtain ⟨t, ht, hsum⟩ := encode (w v) (wsub v)
    exact ⟨t, ht, hsum.trans (wrep v).2⟩
  have indexedCover (v : ZMod q) : ∃ t : Finset (Fin n), t.sum a = v := by
    obtain ⟨t, _, hsum⟩ := windex v
    exact ⟨t, hsum⟩
  have shortSub : shortMod A h q ⊆ FiniteModular.shortResidues a h := by
    intro v hv
    obtain ⟨t, ht, hsum⟩ := windex v
    exact (FiniteModular.mem_shortResidues a h v).mpr
      ⟨t, ht.le.trans (wshort v hv), hsum⟩
  have indexedDense : q ≤ m * (FiniteModular.shortResidues a h).card :=
    dense.trans (Nat.mul_le_mul_left m (Finset.card_le_card shortSub))
  intro v
  obtain ⟨t, ht, hsum⟩ := hb q n a indexedCover indexedDense v
  refine ⟨t.map value, by simpa only [Finset.card_map] using ht, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact Usub _ (e.symm i).property
  · rw [Nat.cast_sum, Finset.sum_map]
    exact hsum

/-- An eventual bound on the number of summands supplies a bounded witness
    in each residue class of every positive modulus. -/
theorem modCover_of_eventually {A : Set ℕ} {t : ℕ}
    (h : ∀ᶠ n in atTop, Rep A t n) (q : ℕ) [NeZero q] (v : ZMod q) :
    ∃ E : Finset ℕ, (∀ x ∈ E, x ∈ A) ∧ E.card ≤ t ∧
      ((E.sum id : ℕ) : ZMod q) = v := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hmul : T ≤ T * q := by
    calc
      T = T * 1 := (Nat.mul_one T).symm
      _ ≤ T * q := Nat.mul_le_mul_left T hq
  have hlarge : T ≤ v.val + T * q := by omega
  obtain ⟨E, hEA, hcard, hsum⟩ := hT (v.val + T * q) hlarge
  refine ⟨E, hEA, hcard, ?_⟩
  rw [hsum]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
    ZMod.natCast_zmod_val]

/-- Correct the target residue with a finite witness. The progression
    hypothesis supplies the remaining summands after deleting that witness. -/
theorem eventually_rep_of_progression {A : Set ℕ} {g : ℕ} [NeZero g]
    (a : ZMod g) (N0 K b : ℕ)
    (cover : ∀ v : ZMod g, ∃ E : Finset ℕ, (∀ x ∈ E, x ∈ A) ∧
      E.card ≤ b ∧ ((E.sum id : ℕ) : ZMod g) = v)
    (progression : ∀ F : Finset ℕ, (∀ x ∈ F, x ∈ A) → F.card ≤ b →
      ∀ n : ℕ, N0 ≤ n → (n : ZMod g) = a → Rep (A \ (F : Set ℕ)) K n) :
    ∀ᶠ n in atTop, Rep A (b + K) n := by
  classical
  let E (v : ZMod g) : Finset ℕ := (cover v).choose
  have hE (v : ZMod g) : (∀ x ∈ E v, x ∈ A) ∧ (E v).card ≤ b ∧
      (((E v).sum id : ℕ) : ZMod g) = v := (cover v).choose_spec
  let M := (Finset.univ : Finset (ZMod g)).sup (fun v => (E v).sum id)
  refine eventually_atTop.mpr ⟨N0 + M, ?_⟩
  intro n hn
  let v : ZMod g := (n : ZMod g) - a
  have hbound : (E v).sum id ≤ M :=
    Finset.le_sup (f := fun r => (E r).sum id) (Finset.mem_univ v)
  have hcost : (E v).sum id ≤ n := by omega
  have hlarge : N0 ≤ n - (E v).sum id := by omega
  have hres : ((n - (E v).sum id : ℕ) : ZMod g) = a := by
    rw [Nat.cast_sub hcost, (hE v).2.2]
    dsimp only [v]
    abel
  obtain ⟨S, hSA, hScard, hSsum⟩ :=
    progression (E v) (hE v).1 (hE v).2.1 _ hlarge hres
  have hd : Disjoint (E v) S := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxE hxS
    exact (hSA x hxS).2 hxE
  refine ⟨E v ∪ S, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with he | hs
    · exact (hE v).1 x he
    · exact (hSA x hs).1
  · rw [Finset.card_union_of_disjoint hd]
    exact Nat.add_le_add (hE v).2.1 hScard
  · rw [Finset.sum_union hd, hSsum]
    exact Nat.add_sub_of_le hcost

/-- The residues of the integer restricted sums have small finite witnesses. -/
theorem shortMod_card_bound {A : Set ℕ} {h m : ℕ}
    (hd : DensityBound (restrictedSums A h) m) (q : ℕ) [NeZero q] :
    q ≤ m * (shortMod A h q).card := by
  classical
  have hblocks := block_density_reduction (restrictedSums A h) m hd q
  apply hblocks.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro v hv
  obtain ⟨n, hn, hnmod⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨s, hsA, hcard, hsum⟩ := hn
  exact (mem_shortMod A h q v).mpr ⟨s, hcard, hsA, by rw [hsum, hnmod]⟩

private theorem no_order_zero (A : Set ℕ) : ¬ HasOrder A 0 := by
  intro h
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  obtain ⟨s, _, hs, hsum⟩ := hT (T + 1) (Nat.le_succ _)
  have hz : s = 0 := Multiset.card_eq_zero.mp (Nat.le_zero.mp hs)
  subst s
  simpa using hsum

/-- The boundedness question in `FormalConjectures.ErdosProblems.«338»`.
The same `f` must work for every basis that already has a restricted order. -/
def BoundedByOrder : Prop :=
  ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
    (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A (f h)

/-- Deduce the boundedness assertion from the two analytic inputs. -/
theorem boundedByOrder_of_analyticInputs
    (density : UniformDensityInput) (progressions : UniformProgressionInput) :
    BoundedByOrder := by
  classical
  have perOrder (h : ℕ) : ∃ k : ℕ, ∀ A : Set ℕ, HasOrder A h →
      (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A k := by
    by_cases hzero : h = 0
    · subst h
      exact ⟨0, fun A hA _ => (no_order_zero A hA).elim⟩
    have hh : 0 < h := Nat.pos_of_ne_zero hzero
    obtain ⟨m, hm, hden⟩ := density h hh
    obtain ⟨b, hmod⟩ := uniformModularForSet h m hm
    obtain ⟨K, hprog⟩ := progressions h m b hh hm
    refine ⟨b + K, ?_⟩
    intro A hA hr
    obtain ⟨t, ht⟩ := hr
    have hd := hden A hA
    obtain ⟨g, hg, a, N₀, hp⟩ := hprog A hd
    letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
    have cover (v : ZMod g) : ∃ s : Finset ℕ, ModRep A g s v := by
      obtain ⟨s, hsA, _, hsum⟩ := modCover_of_eventually ht g v
      exact ⟨s, hsA, hsum⟩
    have shortCover := hmod A g cover (shortMod_card_bound hd g)
    refine eventually_rep_of_progression a N₀ K b ?_ hp
    intro v
    obtain ⟨s, hs, hsA, hsum⟩ := shortCover v
    exact ⟨s, hsA, hs, hsum⟩
  exact ⟨fun h => (perOrder h).choose, fun A h => (perOrder h).choose_spec A⟩

/-- Check the conclusion with both published order predicates expanded. -/
example (density : UniformDensityInput) (progressions : UniformProgressionInput) :
    ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ),
      (∀ᶠ n in atTop, ∃ s : Multiset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum = n) →
      (∃ t : ℕ, ∀ᶠ n in atTop, ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ t ∧ (∑ x ∈ s, x) = n) →
      ∀ᶠ n in atTop, ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ f h ∧ (∑ x ∈ s, x) = n :=
  boundedByOrder_of_analyticInputs density progressions

end Erdos338.Bridge

#check Erdos338.Bridge.boundedByOrder_of_analyticInputs
#print axioms Erdos338.Bridge.boundedByOrder_of_analyticInputs
