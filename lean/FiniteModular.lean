import Mathlib
import MiscYD.AddCombi.Kneser.Kneser

/-! Finite modular lemma for Erdős 338(ii). The intended entry point is
    `uniformModularBound`. The proof uses the two-set Kneser theorem of
    Mantas Bakšys and Yaël Dillies, in MiscYD revision
    cd12c538d66f15a358a6904e7c847cd67661096f. Source draft awaiting a Lean build. -/

namespace Erdos338.FiniteModular

open scoped BigOperators

/-- Each index may occur once. Equal values at different indices are allowed. -/
def Short {ι G : Type*} [AddCommMonoid G] (a : ι → G) (h : ℕ) (x : G) : Prop :=
  ∃ s : Finset ι, s.card ≤ h ∧ s.sum a = x

noncomputable def shortResidues {ι G : Type*} [AddCommMonoid G] [Fintype G]
    (a : ι → G) (h : ℕ) : Finset G := by
  classical
  exact Finset.univ.filter (Short a h)

@[simp] theorem mem_shortResidues {ι G : Type*} [AddCommMonoid G] [Fintype G]
    (a : ι → G) (h : ℕ) (x : G) : x ∈ shortResidues a h ↔ Short a h x := by
  classical
  simp [shortResidues]

/-- We use 1/m as density. For any positive density δ one can choose m ≥ 1/δ.
    The uniform length bound precedes the modulus, sequence length, and sequence. -/
def UniformModularBound : Prop :=
  ∀ h m : ℕ, 0 < m → ∃ b : ℕ,
    ∀ (q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q),
      (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
      q ≤ m * (shortResidues a h).card → ∀ x, Short a b x

/-- Deleting a fixed position translates the represented residue by a fixed amount. -/
theorem column_card {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [Fintype G]
    (R : Finset G) (w : G → Finset ι) (a : ι → G) (j : ℕ)
    (hsum : ∀ r ∈ R, (w r).sum a = r)
    (hsize : ∀ r ∈ R, (w r).card ≤ j + 1) (i : ι) :
    (R.filter (fun r => i ∈ w r)).card ≤ (shortResidues a j).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun r : G => r - a i)
  · intro r hr
    obtain ⟨hrR, hi⟩ := Finset.mem_filter.mp hr
    apply (mem_shortResidues a j _).mpr
    refine ⟨(w r).erase i, ?_, ?_⟩
    · have hc := hsize r hrR
      rw [Finset.card_erase_of_mem hi]
      omega
    · exact eq_sub_iff_add_eq.mpr (((w r).sum_erase_add a hi).trans (hsum r hrR))
  · intro x _ y _ hxy
    simpa only [sub_add_cancel] using congrArg (fun z : G => z + a i) hxy

/-- Count the residues whose selected witnesses touch the forbidden positions. -/
theorem hit_card {ι G : Type*} [DecidableEq ι] [DecidableEq G]
    (R : Finset G) (w : G → Finset ι) (W : Finset ι) (e : ℕ)
    (hcol : ∀ i ∈ W, (R.filter (fun r => i ∈ w r)).card ≤ e) :
    (W.biUnion (fun i => R.filter (fun r => i ∈ w r))).card ≤ W.card * e := by
  calc
    _ ≤ ∑ i ∈ W, (R.filter (fun r => i ∈ w r)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ W, e := Finset.sum_le_sum hcol
    _ = W.card * e := by simp [nsmul_eq_mul]

/-- The choice of x determines y = z-x. Counting x therefore counts ordered pairs. -/
noncomputable def goodLeft {ι G : Type*} [AddCommGroup G]
    (R : Finset G) (w : G → Finset ι) (z : G) : Finset G := by
  classical
  exact R.filter (fun x => z - x ∈ R ∧ Disjoint (w x) (w (z - x)))

/-- A popular residue still has a short witness after forbidding W. -/
theorem avoid_for_popular {ι G : Type*} [DecidableEq ι] [DecidableEq G] [AddCommGroup G]
    (R : Finset G) (w : G → Finset ι) (a : ι → G) (W : Finset ι) (z : G) (j e : ℕ)
    (hsum : ∀ r ∈ R, (w r).sum a = r)
    (hsize : ∀ r ∈ R, (w r).card ≤ j)
    (hcol : ∀ i ∈ W, (R.filter (fun r => i ∈ w r)).card ≤ e)
    (hpop : 2 * (W.card * e) < (goodLeft R w z).card) :
    ∃ s : Finset ι, Disjoint W s ∧ s.card ≤ 2 * j ∧ s.sum a = z := by
  classical
  let H := W.biUnion (fun i => R.filter (fun r => i ∈ w r))
  let H' := H.image (fun y => z - y)
  have hH : H.card ≤ W.card * e := hit_card R w W e hcol
  have hH' : H'.card ≤ H.card := Finset.card_image_le
  have htotal := Finset.card_union_le H H'
  have hlt : (H ∪ H').card < (goodLeft R w z).card := by omega
  obtain ⟨x, hx, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hp : x ∈ R ∧ z - x ∈ R ∧ Disjoint (w x) (w (z - x)) := by
    simpa [goodLeft] using hx
  obtain ⟨hxR, hyR, hdis⟩ := hp
  have havoid (t : G) (ht : t ∈ R) (hnot : t ∉ H) : Disjoint W (w t) := by
    apply Finset.disjoint_left.mpr
    intro i hi hw
    exact hnot (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨ht, hw⟩⟩)
  have hleft := havoid x hxR (fun h => hout (Finset.mem_union_left _ h))
  have hright : Disjoint W (w (z - x)) := by
    apply havoid (z - x) hyR
    intro h
    apply hout
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨z - x, h, by abel⟩
  refine ⟨w x ∪ w (z - x), ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    rcases Finset.mem_union.mp hj with hl | hr
    · exact Finset.disjoint_left.mp hleft hi hl
    · exact Finset.disjoint_left.mp hright hi hr
  · have hc := Finset.card_union_le (w x) (w (z - x))
    have hl := hsize x hxR
    have hr := hsize (z - x) hyR
    omega
  · rw [Finset.sum_union hdis, hsum x hxR, hsum (z - x) hyR]
    abel

/-- Lift increments one at a time, reserving both W and all indices used so far. -/
theorem liftGreedy {ι G : Type*} [DecidableEq ι] [AddCommMonoid G]
    (a : ι → G) (k cap : ℕ) (xs : List G) :
    ∀ W : Finset ι,
      (∀ x ∈ xs, ∀ F : Finset ι, F.card ≤ cap →
        ∃ S : Finset ι, Disjoint F S ∧ S.card ≤ k ∧ S.sum a = x) →
      W.card + k * xs.length ≤ cap →
      ∃ S : Finset ι, Disjoint W S ∧ S.card ≤ k * xs.length ∧
        S.sum a = xs.sum := by
  induction xs with
  | nil =>
    intro W _ _
    exact ⟨∅, by simp, by simp, by simp⟩
  | cons x xs ih =>
    intro W avail room
    simp only [List.length_cons, Nat.mul_succ] at room
    obtain ⟨S, hWS, hSc, hSs⟩ := avail x (by simp) W (by omega)
    have hc := Finset.card_union_le W S
    obtain ⟨T, hUT, hTc, hTs⟩ := ih (W ∪ S)
      (fun y hy => avail y (List.mem_cons_of_mem _ hy)) (by omega)
    have hST : Disjoint S T := Finset.disjoint_left.mpr (by
      intro i hi hj
      exact (Finset.disjoint_left.mp hUT) (Finset.mem_union_right W hi) hj)
    refine ⟨S ∪ T, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      rcases Finset.mem_union.mp hj with hs | ht
      · exact (Finset.disjoint_left.mp hWS) hi hs
      · exact (Finset.disjoint_left.mp hUT) (Finset.mem_union_left S hi) ht
    · have hcard := Finset.card_union_le S T
      simp only [List.length_cons, Nat.mul_succ]
      omega
    · rw [Finset.sum_union hST, hSs, hTs, List.sum_cons]

/-- The mass of the popular fibres forces many distinct popular residues. -/
theorem popularity_card {α : Type*} (s : Finset α)
    (p : α → ℕ) (m q : ℕ) (hq : 0 < q) (hcard : s.card = q)
    (hcap : ∀ z ∈ s, p z ≤ q)
    (hmass : 15*q^2 ≤ 16*m^2*(∑ z ∈ s, p z)) :
    11*q ≤ 16*m^2*(s.filter (fun z => q ≤ 4*m^2*p z)).card := by
  have hpoint (z : α) (hz : z ∈ s) :
      16*m^2*p z ≤ 4*q + (if q ≤ 4*m^2*p z then 16*m^2*q else 0) := by
    by_cases h : q ≤ 4*m^2*p z
    · rw [if_pos h]
      have hb := Nat.mul_le_mul_left (16*m^2) (hcap z hz)
      omega
    · rw [if_neg h, add_zero]
      calc
        16*m^2*p z = 4*(4*m^2*p z) := by ring
        _ ≤ 4*q := Nat.mul_le_mul_left 4 (le_of_lt (lt_of_not_ge h))
  have hupper : 16*m^2*(∑ z ∈ s, p z) ≤ q*(4*q) +
      (s.filter (fun z => q ≤ 4*m^2*p z)).card*(16*m^2*q) := by
    calc
      _ = ∑ z ∈ s, 16*m^2*p z := by rw [Finset.mul_sum]
      _ ≤ ∑ z ∈ s, (4*q + (if q ≤ 4*m^2*p z then 16*m^2*q else 0)) :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.sum_add_distrib,
          ← Finset.sum_filter (s := s) (fun z => q ≤ 4*m^2*p z) (fun _ => 16*m^2*q)]
        simp [nsmul_eq_mul, hcard]
  apply Nat.le_of_mul_le_mul_left (c := q) ?_ hq
  nlinarith only [hmass.trans hupper]

/-- Compress any subset sum to fewer terms than the cardinality of the group.
    This also applies in the quotient group in the stabilizer argument. -/
theorem short_sum {ι G : Type*} [Fintype G] [AddCommMonoid G]
    (f : ι → G) (p : Finset ι) :
    ∃ t ⊆ p, t.sum f = p.sum f ∧ t.card < Fintype.card G := by
  classical
  let R (s : Finset ι) : Finset G :=
    Finset.univ.filter (fun x => ∃ u ⊆ s, u.sum f = x)
  have memR {s : Finset ι} {x : G} :
      x ∈ R s ↔ ∃ u ⊆ s, u.sum f = x := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  have aux (s : Finset ι) : ∀ x ∈ R s,
      ∃ t ⊆ s, t.sum f = x ∧ t.card < (R s).card := by
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      obtain ⟨u, hu, he⟩ := memR.mp hx
      have hu0 : u = ∅ := by simpa using hu
      subst u
      exact ⟨∅, by simp, he, by simpa using Finset.card_pos.mpr ⟨x, hx⟩⟩
    | @insert a s ha ih =>
      intro x hx
      have inc : R s ⊆ R (insert a s) := by
        intro y hy
        obtain ⟨u, hu, he⟩ := memR.mp hy
        exact memR.mpr ⟨u, hu.trans (Finset.subset_insert a s), he⟩
      by_cases old : x ∈ R s
      · obtain ⟨t, ht, he, hc⟩ := ih x old
        exact ⟨t, ht.trans (Finset.subset_insert a s), he,
          lt_of_lt_of_le hc (Finset.card_le_card inc)⟩
      · have grow : (R s).card < (R (insert a s)).card :=
          Finset.card_lt_card ((Finset.ssubset_iff_of_subset inc).mpr ⟨x, hx, old⟩)
        obtain ⟨u, hu, he⟩ := memR.mp hx
        have hau : a ∈ u := by
          by_contra hn
          exact old (memR.mpr ⟨u, (Finset.subset_insert_iff_of_notMem hn).mp hu, he⟩)
        have hus : u.erase a ⊆ s := Finset.subset_insert_iff.mp hu
        obtain ⟨t, ht, et, ct⟩ := ih ((u.erase a).sum f) (memR.mpr ⟨_, hus, rfl⟩)
        have hat : a ∉ t := fun h => ha (ht h)
        refine ⟨insert a t, Finset.insert_subset_insert a ht, ?_, ?_⟩
        · rw [Finset.sum_insert hat, et, Finset.add_sum_erase u f hau, he]
        · rw [Finset.card_insert_of_notMem hat]
          omega
  obtain ⟨t, ht, he, hc⟩ := aux p (p.sum f) (memR.mpr ⟨p, by rfl, rfl⟩)
  exact ⟨t, ht, he, lt_of_lt_of_le hc (Finset.card_le_univ _)⟩

def budget (j m : ℕ) : ℕ := (2*j + 1) * (4*m^2)

def nextDenom (j m : ℕ) : ℕ := 16 * budget j m * m^2

/-- Observe how the density denominator changes before the recursive call. -/
def lengthBound : ℕ → ℕ → ℕ
  | 0, m => m
  | j+1, m => max (lengthBound j (nextDenom (j+1) m)) (budget (j+1) m)

/-- Only the case of sparse shorter sums needs a group argument. -/
def SparseStep : Prop :=
  ∀ (j m q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q), 0 < m →
    (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
    q ≤ m * (shortResidues a (j+1)).card →
    nextDenom (j+1) m * (shortResidues a j).card < q →
    ∀ x, Short a (budget (j+1) m) x

theorem short_mono {ι G : Type*} [AddCommMonoid G] {a : ι → G} {x : G}
    {s t : ℕ} (hst : s ≤ t) (hs : Short a s x) : Short a t x := by
  obtain ⟨U, hU, hx⟩ := hs
  exact ⟨U, hU.trans hst, hx⟩

theorem uniform_of_sparse (step : SparseStep) : UniformModularBound := by
  classical
  have main (h : ℕ) : ∀ m : ℕ, 0 < m →
      ∀ (q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q),
        (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
        q ≤ m * (shortResidues a h).card → ∀ x, Short a (lengthBound h m) x := by
    induction h with
    | zero =>
      intro m hm q inst n a cover dense x
      have hzero : shortResidues a 0 = {0} := by
        ext y
        simp only [mem_shortResidues, Finset.mem_singleton]
        constructor
        · rintro ⟨s, hs, he⟩
          have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
          simpa [hs0] using he.symm
        · rintro rfl
          exact ⟨∅, by simp, by simp⟩
      have hqm : q ≤ m := by simpa [hzero] using dense
      obtain ⟨s, hs⟩ := cover x
      obtain ⟨t, _, he, hc⟩ := short_sum a s
      have hlt : t.card < q := by simpa only [ZMod.card] using hc
      exact ⟨t, hlt.le.trans hqm, he.trans hs⟩
    | succ j ih =>
      intro m hm q inst n a cover dense x
      by_cases hsm : q ≤ nextDenom (j+1) m * (shortResidues a j).card
      · have hpos : 0 < nextDenom (j+1) m := by
          unfold nextDenom budget
          positivity
        exact short_mono (le_max_left _ _) (ih _ hpos q n a cover hsm x)
      · exact short_mono (le_max_right _ _)
          (step j m q n a hm cover dense (lt_of_not_ge hsm) x)
  intro h m hm
  exact ⟨lengthBound h m, main h m hm⟩

/-- The finite-group conclusion needed to join the counting argument to the lift. -/
def DenseSplit : Prop :=
  ∀ (q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q) (D : Finset (ZMod q)) (L : ℕ),
    0 ∈ D → 2*q ≤ L*D.card → (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
    ∀ x, ∃ (E : Finset (Fin n)) (xs : List (ZMod q)),
      E.card ≤ L ∧ xs.length ≤ L ∧ (∀ d ∈ xs, d ∈ D) ∧ E.sum a + xs.sum = x

/-- Every ordered pair of residues either gives a disjoint pair in its sum
    fibre or its second witness meets an index of the first witness. -/
theorem goodLeft_mass {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [Fintype G]
    (R : Finset G) (w : G → Finset ι) (j e : ℕ)
    (hsize : ∀ x ∈ R, (w x).card ≤ j)
    (hcol : ∀ i, (R.filter (fun y => i ∈ w y)).card ≤ e) :
    R.card ^ 2 ≤ (∑ z : G, (goodLeft R w z).card) + R.card * (j * e) := by
  classical
  let Q (x : G) := Finset.univ.filter (fun z => x ∈ goodLeft R w z)
  have row (x : G) (hx : x ∈ R) : R.card ≤ (Q x).card + j * e := by
    let H := (w x).biUnion (fun i => R.filter (fun y => i ∈ w y))
    have hH : H.card ≤ j * e :=
      (hit_card R w (w x) e (fun i _ => hcol i)).trans
        (Nat.mul_le_mul_right e (hsize x hx))
    have hrest : (R \ H).card ≤ (Q x).card := by
      apply Finset.card_le_card_of_injOn (fun y : G => x + y)
      · intro y hy
        obtain ⟨hyR, hyH⟩ := Finset.mem_sdiff.mp hy
        have hd : Disjoint (w x) (w y) := Finset.disjoint_left.mpr (by
          intro i hi hiy
          exact hyH (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hyR, hiy⟩⟩))
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have he : x + y - x = y := by abel
        simpa only [goodLeft, Finset.mem_filter, he] using
          (show x ∈ R ∧ y ∈ R ∧ Disjoint (w x) (w y) from ⟨hx, hyR, hd⟩)
      · intro a _ b _ hab
        exact add_left_cancel hab
    have hsub : R ⊆ (R \ H) ∪ H := by
      intro y hy
      by_cases hyH : y ∈ H
      · exact Finset.mem_union_right _ hyH
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy, hyH⟩)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hrest hH))
  have count (s : Finset G) (p : G → Prop) [DecidablePred p] :
      (s.filter p).card = ∑ x ∈ s, if p x then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  have fibre (z : G) : R.filter (fun x => x ∈ goodLeft R w z) = goodLeft R w z := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      have hp : x ∈ R ∧ z - x ∈ R ∧ Disjoint (w x) (w (z - x)) := by
        simpa only [goodLeft, Finset.mem_filter] using hx
      exact Finset.mem_filter.mpr ⟨hp.1, hx⟩
  have doubleCount : (∑ x ∈ R, (Q x).card) = ∑ z : G, (goodLeft R w z).card := by
    calc
      _ = ∑ x ∈ R, ∑ z : G, if x ∈ goodLeft R w z then (1 : ℕ) else 0 :=
        Finset.sum_congr rfl (fun x _ => count Finset.univ _)
      _ = ∑ z : G, ∑ x ∈ R, if x ∈ goodLeft R w z then (1 : ℕ) else 0 :=
        Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun z _ =>
        (count R (fun x => x ∈ goodLeft R w z)).symm.trans (congrArg Finset.card (fibre z)))
  calc
    R.card ^ 2 = ∑ _x ∈ R, R.card := by simp [pow_two, nsmul_eq_mul]
    _ ≤ ∑ x ∈ R, ((Q x).card + j * e) := Finset.sum_le_sum row
    _ = _ := by rw [Finset.sum_add_distrib, doubleCount]; simp [nsmul_eq_mul]

/-- When shorter witnesses are sparse, most pairs of chosen witnesses are disjoint.
    This estimate clears all denominators before making the comparison. -/
private theorem mass_estimate (q m M j e S P : ℕ)
    (hdense : q ≤ m*M) (hM : M ≤ q) (hj : j ≤ S)
    (hsparse : 16*S*m^2*e < q) (hcount : M^2 ≤ P + M*(j*e)) :
    15*q^2 ≤ 16*m^2*P := by
  have hs : q*q ≤ (m*M)*(m*M) := Nat.mul_le_mul hdense hdense
  have hje : 16*j*m^2*e ≤ q := by
    calc
      _ ≤ 16*S*m^2*e := by gcongr
      _ ≤ q := hsparse.le
  have hloss := Nat.mul_le_mul hM hje
  have hcount' := Nat.mul_le_mul_left (16*m^2) hcount
  nlinarith only [hs, hloss, hcount']

theorem sparse_of_denseSplit (split : DenseSplit) : SparseStep := by
  classical
  intro j m q inst n a hm cover dense sparse x
  let J := j+1
  let R := shortResidues a J
  let e := (shortResidues a j).card
  let L := 4*m^2
  let S := budget J m
  have hS : S = (2*J+1)*L := rfl
  have hL : 0 < L := by dsimp [L]; positivity
  have hJS : J ≤ S := by
    rw [hS]
    calc
      J ≤ 2*J+1 := by omega
      _ = (2*J+1)*1 := by simp
      _ ≤ (2*J+1)*L := Nat.mul_le_mul_left _ hL
  have hsp : 16*S*m^2*e < q := sparse
  have hR (u : ZMod q) (hu : u ∈ R) : Short a J u :=
    (mem_shortResidues a J u).mp hu
  let w (u : ZMod q) : Finset (Fin n) :=
    if hu : u ∈ R then (hR u hu).choose else ∅
  have hw (u : ZMod q) (hu : u ∈ R) :
      (w u).card ≤ J ∧ (w u).sum a = u := by
    simpa only [w, dif_pos hu] using (hR u hu).choose_spec
  have size := fun u hu => (hw u hu).1
  have sums := fun u hu => (hw u hu).2
  have col (i : Fin n) : (R.filter (fun u => i ∈ w u)).card ≤ e :=
    column_card R w a j sums size i
  let p (d : ZMod q) := (goodLeft R w d).card
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : R.card ≤ q := by simpa only [ZMod.card] using Finset.card_le_univ R
  have mass : 15*q^2 ≤ 16*m^2*(∑ d, p d) :=
    mass_estimate q m R.card J e S _ dense hM hJS hsp
      (goodLeft_mass R w J e size col)
  let P := Finset.univ.filter (fun d : ZMod q => q ≤ 4*m^2*p d)
  let D := insert 0 P
  have hP : 11*q ≤ 16*m^2*P.card :=
    popularity_card Finset.univ p m q hq (by simp [ZMod.card])
      (fun d _ => by simpa only [ZMod.card] using Finset.card_le_univ (goodLeft R w d)) mass
  have hPD : P.card ≤ D.card := Finset.card_le_card (Finset.subset_insert _ _)
  have hD : 2*q ≤ L*D.card := by
    dsimp [L]
    nlinarith only [hP, Nat.mul_le_mul_left (16*m^2) hPD, Nat.zero_le q]
  obtain ⟨E, xs, hE, hxs, hmem, hx⟩ :=
    split q n a D L (Finset.mem_insert_self _ _) hD cover x
  have avail (d : ZMod q) (hd : d ∈ xs) (W : Finset (Fin n)) (hW : W.card ≤ S) :
      ∃ T : Finset (Fin n), Disjoint W T ∧ T.card ≤ 2*J ∧ T.sum a = d := by
    rcases Finset.mem_insert.mp (hmem d hd) with hz | hpop
    · subst d
      exact ⟨∅, by simp, by simp, by simp⟩
    · have hpd : q ≤ 4*m^2*p d := (Finset.mem_filter.mp hpop).2
      apply avoid_for_popular R w a W d J e sums size (fun i _ => col i)
      change 2 * (W.card * e) < p d
      by_contra! hbad
      have hc : q ≤ 16*S*m^2*e := calc
        q ≤ 4*m^2*p d := hpd
        _ ≤ 4*m^2*(2*(W.card*e)) := Nat.mul_le_mul_left _ hbad
        _ = 8*W.card*m^2*e := by ring
        _ ≤ 16*S*m^2*e := by gcongr <;> norm_num
      exact (Nat.not_le_of_gt hsp) hc
  have hroom : E.card + (2*J)*xs.length ≤ S := calc
    _ ≤ L + (2*J)*L := Nat.add_le_add hE (Nat.mul_le_mul_left _ hxs)
    _ = S := by rw [hS]; ring
  obtain ⟨T, hdis, hT, hsum⟩ := liftGreedy a (2*J) S xs E avail hroom
  refine ⟨E ∪ T, ?_, ?_⟩
  · exact (Finset.card_union_le E T).trans
      ((Nat.add_le_add_left hT E.card).trans hroom)
  · rw [Finset.sum_union hdis, hsum, hx]

open scoped Pointwise

/-- The residues that are sums of exactly `k` terms of `D`, with repetition. -/
noncomputable def sumLayer {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (D : Finset G) : ℕ → Finset G
  | 0 => {0}
  | k+1 => sumLayer D k + D

theorem zero_mem_sumLayer {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (D : Finset G) (hD : 0 ∈ D) (k : ℕ) : 0 ∈ sumLayer D k := by
  induction k with
  | zero => simp [sumLayer]
  | succ k ih =>
    change 0 ∈ sumLayer D k + D
    exact Finset.mem_add.mpr ⟨0, ih, 0, hD, zero_add _⟩

theorem word_of_mem_sumLayer {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (D : Finset G) (k : ℕ) {z : G} (hz : z ∈ sumLayer D k) :
    ∃ xs : List G, xs.length = k ∧ (∀ d ∈ xs, d ∈ D) ∧ xs.sum = z := by
  induction k generalizing z with
  | zero =>
    have hzero : z = 0 := Finset.mem_singleton.mp hz
    exact ⟨[], rfl, by simp, by simp [hzero]⟩
  | succ k ih =>
    change z ∈ sumLayer D k + D at hz
    obtain ⟨y, hy, d, hd, heq⟩ := Finset.mem_add.mp hz
    obtain ⟨ys, hlen, hmem, hsum⟩ := ih hy
    refine ⟨d :: ys, by simp [hlen], ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hd
      · exact hmem b hb'
    · rw [List.sum_cons, hsum, add_comm, heq]

/-- Weak iterated Kneser for positive numbers of identical summands containing zero.
    The subgroup consists of periods of the final sumset. -/
def IteratedKneser : Prop :=
  ∀ (q : ℕ) [NeZero q] (D : Finset (ZMod q)) (L : ℕ), 0 ∈ D → 0 < L →
    ∃ H : AddSubgroup (ZMod q),
      (∀ h ∈ H, ∀ y ∈ sumLayer D L, y + h ∈ sumLayer D L) ∧
      L * D.card ≤ (sumLayer D L).card + (L-1) * Nat.card H

/-- Density bounds the index of the period subgroup. Compress a representing
    subset in the quotient, then express its error as a word in `D`. -/
theorem denseSplit_of_iteratedKneser (kneser : IteratedKneser) : DenseSplit := by
  classical
  intro q inst n a D L hD dense cover x
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hL : 0 < L := by
    by_contra hn
    have hzero : L = 0 := by omega
    rw [hzero, zero_mul] at dense
    omega
  obtain ⟨H, period, bound⟩ := kneser q D L hD hL
  have hsize : (sumLayer D L).card ≤ q := by
    simpa only [ZMod.card] using Finset.card_le_univ (sumLayer D L)
  have hmul : q ≤ L * Nat.card H := by
    have hle := Nat.mul_le_mul_right (Nat.card H) (Nat.sub_le L 1)
    omega
  have hprod : Nat.card (ZMod q ⧸ H) * Nat.card H = q := by
    simpa only [Nat.card_zmod] using H.card_eq_card_quotient_mul_card_addSubgroup.symm
  have hindex : Fintype.card (ZMod q ⧸ H) ≤ L := by
    rw [← Nat.card_eq_fintype_card]
    by_contra! hlt
    have hp := Nat.mul_lt_mul_of_pos_right hlt (Nat.card_pos (α := H))
    omega
  let π : ZMod q →+ (ZMod q ⧸ H) := QuotientAddGroup.mk' H
  obtain ⟨s, hs⟩ := cover x
  obtain ⟨E, _, hEs, hEcard⟩ := short_sum (fun i => π (a i)) s
  have hcoset : π x = π (E.sum a) := by
    calc
      π x = π (s.sum a) := congrArg π hs.symm
      _ = π (E.sum a) := by simpa only [map_sum] using hEs.symm
  have herr : x - E.sum a ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp hcoset
  have hword : x - E.sum a ∈ sumLayer D L := by
    simpa only [zero_add] using
      period (x - E.sum a) herr 0 (zero_mem_sumLayer D hD L)
  obtain ⟨xs, hlen, hmem, hsum⟩ := word_of_mem_sumLayer D L hword
  exact ⟨E, xs, hEcard.le.trans hindex, hlen.le, hmem, by rw [hsum]; abel⟩

open scoped Pointwise

/-- The two-summand Kneser inequality, in the finite cyclic groups used here. -/
def BinaryKneser : Prop :=
  ∀ (q : ℕ) [NeZero q] (s t : Finset (ZMod q)),
    (s + (s + t).addStab).card + (t + (s + t).addStab).card ≤
      (s + t).card + (s + t).addStab.card

private theorem binaryKneser_card (kneser : BinaryKneser)
    (q : ℕ) [NeZero q] (s t : Finset (ZMod q)) (hne : (s + t).Nonempty) :
    s.card + t.card ≤ (s + t).card + Nat.card (AddAction.stabilizer (ZMod q) (s + t)) := by
  let P := (s + t).addStab
  let H := AddAction.stabilizer (ZMod q) (s + t)
  have hz : (0 : ZMod q) ∈ P := by
    apply (Finset.mem_addStab hne).mpr
    simp
  have pad (B : Finset (ZMod q)) : B.card ≤ (B + P).card := by
    apply Finset.card_le_card
    intro b hb
    simpa only [add_zero] using Finset.add_mem_add hb hz
  have hP : P.card ≤ Nat.card H := by
    rw [← Nat.card_eq_finsetCard P]
    let f (p : P) : H :=
      ⟨p.val, AddAction.mem_stabilizer_iff.mpr ((Finset.mem_addStab hne).mp p.property)⟩
    apply Nat.card_le_card_of_injective f
    intro x y hxy
    exact Subtype.ext (congrArg (fun g : H => g.val) hxy)
  calc
    s.card + t.card ≤ (s + P).card + (t + P).card := Nat.add_le_add (pad s) (pad t)
    _ ≤ (s + t).card + P.card := kneser q s t
    _ ≤ (s + t).card + Nat.card H := Nat.add_le_add_left hP _

/-- Every translation fixing the first summand fixes the sumset. -/
private theorem sumset_stabilizer_mono {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A D : Finset G) : AddAction.stabilizer G A ≤ AddAction.stabilizer G (A + D) := by
  intro h hh
  have hfix := AddAction.mem_stabilizer_iff.mp hh
  apply AddAction.mem_stabilizer_iff.mpr
  calc
    h +ᵥ (A + D) = ({h} : Finset G) + (A + D) := (Finset.singleton_add h).symm
    _ = (({h} : Finset G) + A) + D := (add_assoc _ _ _).symm
    _ = A + D := by rw [Finset.singleton_add, hfix]

/-- Iterate the binary inequality while enlarging each error term to the
    cardinality of the stabilizer of the new layer. -/
theorem iteratedKneser_of_binaryKneser (kneser : BinaryKneser) : IteratedKneser := by
  intro q _ D L hD hL
  let St (A : Finset (ZMod q)) := AddAction.stabilizer (ZMod q) A
  have bound (k : ℕ) : (k+1) * D.card ≤ (sumLayer D (k+1)).card +
      k * Nat.card (St (sumLayer D (k+1))) := by
    induction k with
    | zero =>
      have oneLayer : sumLayer D 1 = D := by
        change ({0} : Finset (ZMod q)) + D = D
        rw [Finset.singleton_add, zero_vadd]
      simp [oneLayer]
    | succ k ih =>
      let A := sumLayer D (k+1)
      have hA : 0 ∈ A := zero_mem_sumLayer D hD (k+1)
      have hstep := binaryKneser_card kneser q A D ⟨0+0, Finset.add_mem_add hA hD⟩
      have hmono := sumset_stabilizer_mono A D
      have hc : Nat.card (St A) ≤ Nat.card (St (A+D)) := by
        let f (h : St A) : St (A+D) := ⟨h.val, hmono h.property⟩
        apply Nat.card_le_card_of_injective f
        intro x y hxy
        exact Subtype.ext (congrArg (fun g : St (A+D) => g.val) hxy)
      have hmul := Nat.mul_le_mul_left k hc
      change (k+1) * D.card ≤ A.card + k * Nat.card (St A) at ih
      change A.card + D.card ≤ (A+D).card + Nat.card (St (A+D)) at hstep
      change (k+1+1) * D.card ≤ (A+D).card + (k+1) * Nat.card (St (A+D))
      rw [Nat.succ_mul (k+1) D.card, Nat.succ_mul k (Nat.card (St (A+D)))]
      omega
  refine ⟨St (sumLayer D L), ?_, ?_⟩
  · intro h hh y hy
    have hm : h+y ∈ h +ᵥ sumLayer D L := Finset.vadd_mem_vadd_finset hy
    rw [AddAction.mem_stabilizer_iff.mp hh] at hm
    simpa only [add_comm h y] using hm
  · cases L with
    | zero => omega
    | succ k => simpa using bound k

/-- Uniform in both the modulus and the number of positions in the sequence. -/
theorem uniformModularBound : UniformModularBound := by
  apply uniform_of_sparse
  apply sparse_of_denseSplit
  apply denseSplit_of_iteratedKneser
  apply iteratedKneser_of_binaryKneser
  intro q inst s t
  exact Finset.add_kneser s t

#print axioms uniformModularBound

end Erdos338.FiniteModular
