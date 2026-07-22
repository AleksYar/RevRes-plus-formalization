import Revres.ApproxDegree.Multilinearize
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp

/-!
# Finite symmetrization and Boolean slice polynomials

Boolean assignments are identified with their supports, coordinate permutations are averaged
explicitly, and multilinear monomials are averaged over fixed-weight slices.  The resulting slice
values are represented by a univariate polynomial in the binomial basis.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace ApproxDegree

/-- Coordinates equal to one in a Boolean assignment. -/
def booleanSupport {m : ℕ} (x : Fin m → F2) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ x i = 1

@[simp]
theorem mem_booleanSupport {m : ℕ} (x : Fin m → F2) (i : Fin m) :
    i ∈ booleanSupport x ↔ x i = 1 := by
  simp [booleanSupport]

/-- Hamming weight on the generic `m`-dimensional Boolean cube. -/
def booleanWeight {m : ℕ} (x : Fin m → F2) : ℕ :=
  (booleanSupport x).card

/-- The real-valued OR function on a generic Boolean cube. -/
def orValue {m : ℕ} (x : Fin m → F2) : ℝ :=
  if booleanWeight x = 0 then 0 else 1

@[simp]
theorem orValue_eq_zero_of_booleanWeight_eq_zero {m : ℕ}
    (x : Fin m → F2) (hzero : booleanWeight x = 0) :
    orValue x = 0 := by
  simp [orValue, hzero]

@[simp]
theorem orValue_eq_one_of_booleanWeight_pos {m : ℕ}
    (x : Fin m → F2) (hpos : 0 < booleanWeight x) :
    orValue x = 1 := by
  simp [orValue, Nat.ne_of_gt hpos]

/-- The Boolean assignment whose one-set is exactly `s`. -/
def assignmentOfSupport {m : ℕ} (s : Finset (Fin m)) : Fin m → F2 :=
  fun i ↦ if i ∈ s then 1 else 0

@[simp]
theorem booleanSupport_assignmentOfSupport {m : ℕ}
    (s : Finset (Fin m)) :
    booleanSupport (assignmentOfSupport s) = s := by
  ext i
  simp [assignmentOfSupport]

@[simp]
theorem assignmentOfSupport_booleanSupport {m : ℕ}
    (x : Fin m → F2) :
    assignmentOfSupport (booleanSupport x) = x := by
  funext i
  rcases F2_eq_zero_or_one (x i) with hzero | hone
  · simp [assignmentOfSupport, hzero]
  · simp [assignmentOfSupport, hone]

/-- Boolean assignments are equivalent to their finite sets of one-coordinates. -/
def booleanSupportEquiv (m : ℕ) :
    (Fin m → F2) ≃ Finset (Fin m) where
  toFun := booleanSupport
  invFun := assignmentOfSupport
  left_inv := assignmentOfSupport_booleanSupport
  right_inv := booleanSupport_assignmentOfSupport

/-- Boolean assignments of Hamming weight exactly `j`. -/
def weightSlice (m j : ℕ) : Finset (Fin m → F2) :=
  Finset.univ.filter fun x ↦ booleanWeight x = j

@[simp]
theorem mem_weightSlice {m j : ℕ} (x : Fin m → F2) :
    x ∈ weightSlice m j ↔ booleanWeight x = j := by
  simp [weightSlice]

/-- Restrict support equivalence to assignments and coordinate sets of cardinality `j`. -/
def weightSliceEquiv (m j : ℕ) :
    ↑(weightSlice m j) ≃
      ↑((Finset.univ : Finset (Fin m)).powersetCard j) where
  toFun x := ⟨booleanSupport x.1, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      simpa [booleanWeight] using (mem_weightSlice x.1).mp x.2⟩⟩
  invFun s := ⟨assignmentOfSupport s.1, by
    rw [mem_weightSlice, booleanWeight, booleanSupport_assignmentOfSupport]
    exact (Finset.mem_powersetCard.mp s.2).2⟩
  left_inv x := by
    apply Subtype.ext
    exact assignmentOfSupport_booleanSupport x.1
  right_inv s := by
    apply Subtype.ext
    exact booleanSupport_assignmentOfSupport s.1

theorem card_weightSlice (m j : ℕ) :
    (weightSlice m j).card = m.choose j := by
  calc
    (weightSlice m j).card = Fintype.card ↑(weightSlice m j) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
          ↑((Finset.univ : Finset (Fin m)).powersetCard j) :=
      Fintype.card_congr (weightSliceEquiv m j)
    _ = ((Finset.univ : Finset (Fin m)).powersetCard j).card :=
      Fintype.card_coe _
    _ = m.choose j := by
      rw [Finset.card_powersetCard]
      simp

theorem weightSlice_nonempty {m j : ℕ} (hj : j ≤ m) :
    (weightSlice m j).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_weightSlice]
  exact Nat.choose_pos hj

/-- Uniform finite average of a polynomial over one Hamming-weight slice. -/
noncomputable def sliceAverage {m : ℕ}
    (p : BooleanPolynomial m) (j : ℕ) : ℝ :=
  (∑ x ∈ weightSlice m j, evalBoolean x p) /
    ((weightSlice m j).card : ℝ)

theorem abs_sliceAverage_sub_le {m j : ℕ}
    {p : BooleanPolynomial m} {c epsilon : ℝ}
    (hj : j ≤ m)
    (h : ∀ x, x ∈ weightSlice m j →
      |evalBoolean x p - c| ≤ epsilon) :
    |sliceAverage p j - c| ≤ epsilon := by
  let s := weightSlice m j
  have hs : s.Nonempty := weightSlice_nonempty hj
  have hcardNat : 0 < s.card := hs.card_pos
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hcardNat
  obtain ⟨x, hx⟩ := hs
  have hepsilon : 0 ≤ epsilon :=
    (abs_nonneg (evalBoolean x p - c)).trans (h x hx)
  have hsum :
      |∑ x ∈ s, (evalBoolean x p - c)| ≤
        (s.card : ℝ) * epsilon := by
    calc
      |∑ x ∈ s, (evalBoolean x p - c)| ≤
          ∑ x ∈ s, |evalBoolean x p - c| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ s, epsilon := by
        apply Finset.sum_le_sum
        intro y hy
        exact h y hy
      _ = (s.card : ℝ) * epsilon := by
        simp
  have havgSub :
      sliceAverage p j - c =
        (∑ x ∈ s, (evalBoolean x p - c)) / (s.card : ℝ) := by
    unfold sliceAverage
    change (∑ x ∈ s, evalBoolean x p) / (s.card : ℝ) - c = _
    field_simp
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  rw [havgSub, abs_div, abs_of_pos hcard]
  apply (div_le_iff₀ hcard).2
  simpa [mul_comm] using hsum

/-! ## Coordinate permutations and finite symmetrization -/

/-- Precomposition of a Boolean assignment by a coordinate permutation. -/
def permuteAssignment {m : ℕ}
    (sigma : Equiv.Perm (Fin m)) (x : Fin m → F2) : Fin m → F2 :=
  fun i ↦ x (sigma i)

/-- Rename the variables of a Boolean polynomial by a coordinate permutation. -/
noncomputable def permutePolynomial {m : ℕ}
    (sigma : Equiv.Perm (Fin m)) (p : BooleanPolynomial m) :
    BooleanPolynomial m :=
  MvPolynomial.rename sigma p

@[simp]
theorem evalBoolean_permutePolynomial {m : ℕ}
    (sigma : Equiv.Perm (Fin m)) (p : BooleanPolynomial m)
    (x : Fin m → F2) :
    evalBoolean x (permutePolynomial sigma p) =
      evalBoolean (permuteAssignment sigma x) p := by
  simp [evalBoolean, permutePolynomial, permuteAssignment, MvPolynomial.eval_rename,
    Function.comp_def]

/-- A coordinate permutation preserves Hamming weight. -/
@[simp]
theorem booleanWeight_permuteAssignment {m : ℕ}
    (sigma : Equiv.Perm (Fin m)) (x : Fin m → F2) :
    booleanWeight (permuteAssignment sigma x) = booleanWeight x := by
  let e : ↑(booleanSupport (permuteAssignment sigma x)) ≃ ↑(booleanSupport x) :=
    { toFun := fun i ↦ ⟨sigma i.1, by
        apply (mem_booleanSupport _ _).2
        have hi := (mem_booleanSupport _ _).1 i.2
        change x (sigma i.1) = 1 at hi
        exact hi⟩
      invFun := fun i ↦ ⟨sigma.symm i.1, by
        apply (mem_booleanSupport _ _).2
        simp only [permuteAssignment, sigma.apply_symm_apply]
        exact (mem_booleanSupport _ _).1 i.2⟩
      left_inv := fun i ↦ by ext; simp
      right_inv := fun i ↦ by ext; simp }
  unfold booleanWeight
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr e

theorem totalDegree_permutePolynomial {m : ℕ}
    (sigma : Equiv.Perm (Fin m)) (p : BooleanPolynomial m) :
    (permutePolynomial sigma p).totalDegree = p.totalDegree := by
  simpa [permutePolynomial, MvPolynomial.renameEquiv_apply] using
    MvPolynomial.totalDegree_renameEquiv (R := ℝ) sigma p

/-- The exact average of a polynomial over all coordinate permutations. -/
noncomputable def symmetrize {m : ℕ}
    (p : BooleanPolynomial m) : BooleanPolynomial m :=
  ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) •
    ∑ sigma : Equiv.Perm (Fin m), permutePolynomial sigma p

theorem totalDegree_symmetrize_le {m : ℕ}
    (p : BooleanPolynomial m) :
    (symmetrize p).totalDegree ≤ p.totalDegree := by
  unfold symmetrize
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  apply MvPolynomial.totalDegree_finsetSum_le
  intro sigma _
  exact (totalDegree_permutePolynomial sigma p).le

theorem isSymmetric_symmetrize {m : ℕ}
    (p : BooleanPolynomial m) :
    (symmetrize p).IsSymmetric := by
  intro tau
  unfold symmetrize permutePolynomial
  simp only [map_smul, map_sum, MvPolynomial.rename_rename]
  congr 1
  simpa [Equiv.Perm.mul_apply] using
    (Equiv.sum_comp (Equiv.mulLeft tau)
      (fun sigma : Equiv.Perm (Fin m) ↦ MvPolynomial.rename sigma p))

theorem multilinear_permutePolynomial {m : ℕ}
    {p : BooleanPolynomial m} (hp : p.Multilinear)
    (sigma : Equiv.Perm (Fin m)) :
    (permutePolynomial sigma p).Multilinear := by
  intro i
  rw [← sigma.apply_symm_apply i]
  simpa [permutePolynomial] using
    (MvPolynomial.degreeOf_rename_of_injective sigma.injective (sigma.symm i)).le.trans
      (hp (sigma.symm i))

theorem multilinear_symmetrize {m : ℕ}
    {p : BooleanPolynomial m} (hp : p.Multilinear) :
    (symmetrize p).Multilinear := by
  have hsum :
      (∑ sigma : Equiv.Perm (Fin m), permutePolynomial sigma p).Multilinear := by
    classical
    let s := (Finset.univ : Finset (Equiv.Perm (Fin m)))
    change BooleanPolynomial.Multilinear
      (∑ sigma ∈ s, permutePolynomial sigma p)
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        simpa using (BooleanPolynomial.Multilinear.C (N := m) 0)
    | @insert sigma s hsigma ih =>
        rw [Finset.sum_insert hsigma]
        exact BooleanPolynomial.Multilinear.add
          (multilinear_permutePolynomial hp sigma) ih
  intro i
  unfold symmetrize
  rw [MvPolynomial.smul_eq_C_mul]
  change (MvPolynomial.C
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
      ∑ sigma : Equiv.Perm (Fin m), permutePolynomial sigma p).degreeOf i ≤ 1
  exact (MvPolynomial.degreeOf_C_mul_le _ i _).trans (hsum i)

/-- Equal-weight Boolean assignments differ by a coordinate permutation. -/
theorem exists_permutation_of_booleanWeight_eq {m : ℕ}
    {x y : Fin m → F2} (hweight : booleanWeight x = booleanWeight y) :
    ∃ sigma : Equiv.Perm (Fin m), permuteAssignment sigma x = y := by
  classical
  let px : Fin m → Prop := fun i ↦ i ∈ booleanSupport x
  let py : Fin m → Prop := fun i ↦ i ∈ booleanSupport y
  let ex : {i // px i} ≃ ↑(booleanSupport x) :=
    { toFun := fun i ↦ ⟨i.1, by
        have hi := i.2
        change i.1 ∈ booleanSupport x at hi
        exact hi⟩
      invFun := fun i ↦ ⟨i.1, by
        change i.1 ∈ booleanSupport x
        exact i.2⟩
      left_inv := fun i ↦ by ext; rfl
      right_inv := fun i ↦ by ext; rfl }
  let ey : {i // py i} ≃ ↑(booleanSupport y) :=
    { toFun := fun i ↦ ⟨i.1, by
        have hi := i.2
        change i.1 ∈ booleanSupport y at hi
        exact hi⟩
      invFun := fun i ↦ ⟨i.1, by
        change i.1 ∈ booleanSupport y
        exact i.2⟩
      left_inv := fun i ↦ by ext; rfl
      right_inv := fun i ↦ by ext; rfl }
  have hOne : Fintype.card {i // py i} = Fintype.card {i // px i} := by
    calc
      Fintype.card {i // py i} = Fintype.card ↑(booleanSupport y) :=
        Fintype.card_congr ey
      _ = Fintype.card ↑(booleanSupport x) := by
        rw [Fintype.card_coe, Fintype.card_coe]
        exact hweight.symm
      _ = Fintype.card {i // px i} := (Fintype.card_congr ex).symm
  let eOne : {i // py i} ≃ {i // px i} := Fintype.equivOfCardEq hOne
  have hZero : Fintype.card {i // ¬ py i} = Fintype.card {i // ¬ px i} :=
    Fintype.card_compl_eq_card_compl py px hOne
  let eZero : {i // ¬ py i} ≃ {i // ¬ px i} := Fintype.equivOfCardEq hZero
  let sigma : Equiv.Perm (Fin m) :=
    (Equiv.sumCompl py).symm |>.trans
      ((eOne.sumCongr eZero).trans (Equiv.sumCompl px))
  refine ⟨sigma, funext fun i ↦ ?_⟩
  rcases F2_eq_zero_or_one (y i) with hy | hy
  · have hi : ¬ py i := by
      intro hi
      exact zero_ne_one (hy.symm.trans ((mem_booleanSupport y i).1 hi))
    have hsigma : sigma i = (eZero ⟨i, hi⟩).1 := by
      simp [sigma, Equiv.sumCompl_symm_apply_of_neg hi]
    have hnotOne : x (sigma i) ≠ 1 := by
      intro hone
      have hmem : sigma i ∈ booleanSupport x := (mem_booleanSupport x _).2 hone
      rw [hsigma] at hmem
      exact (eZero ⟨i, hi⟩).2 hmem
    rcases F2_eq_zero_or_one (x (sigma i)) with hzero | hone
    · simp [permuteAssignment, hzero, hy]
    · exact (hnotOne hone).elim
  · have hi : py i := by
      exact (mem_booleanSupport y i).2 hy
    have hsigma : sigma i = (eOne ⟨i, hi⟩).1 := by
      simp [sigma, Equiv.sumCompl_symm_apply_of_pos hi]
    have hone : x (sigma i) = 1 := by
      apply (mem_booleanSupport x _).1
      rw [hsigma]
      exact (eOne ⟨i, hi⟩).2
    simp [permuteAssignment, hone, hy]

theorem eval_symmetrize_depends_only_on_weight {m : ℕ}
    (p : BooleanPolynomial m) {x y : Fin m → F2}
    (hweight : booleanWeight x = booleanWeight y) :
    evalBoolean x (symmetrize p) = evalBoolean y (symmetrize p) := by
  obtain ⟨sigma, hsigma⟩ := exists_permutation_of_booleanWeight_eq hweight
  calc
    evalBoolean x (symmetrize p) =
        evalBoolean x (permutePolynomial sigma (symmetrize p)) := by
      change evalBoolean x (symmetrize p) =
        evalBoolean x (MvPolynomial.rename sigma (symmetrize p))
      rw [isSymmetric_symmetrize p sigma]
    _ = evalBoolean (permuteAssignment sigma x) (symmetrize p) :=
      evalBoolean_permutePolynomial sigma (symmetrize p) x
    _ = evalBoolean y (symmetrize p) := by rw [hsigma]

/-- Coordinate precomposition as an equivalence of the whole Boolean cube. -/
def permuteAssignmentEquiv {m : ℕ} (sigma : Equiv.Perm (Fin m)) :
    (Fin m → F2) ≃ (Fin m → F2) where
  toFun := permuteAssignment sigma
  invFun := permuteAssignment sigma.symm
  left_inv x := by
    funext i
    simp [permuteAssignment]
  right_inv x := by
    funext i
    simp [permuteAssignment]

/-- A coordinate permutation restricts to an equivalence of each weight slice. -/
def weightSlicePermutationEquiv {m : ℕ}
    (sigma : Equiv.Perm (Fin m)) (j : ℕ) :
    ↑(weightSlice m j) ≃ ↑(weightSlice m j) where
  toFun x := ⟨permuteAssignment sigma x.1, by
    rw [mem_weightSlice, booleanWeight_permuteAssignment]
    exact (mem_weightSlice x.1).1 x.2⟩
  invFun x := ⟨permuteAssignment sigma.symm x.1, by
    rw [mem_weightSlice, booleanWeight_permuteAssignment]
    exact (mem_weightSlice x.1).1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp [permuteAssignment]
  right_inv x := by
    apply Subtype.ext
    funext i
    simp [permuteAssignment]

theorem sum_weightSlice_permuteAssignment {m j : ℕ}
    (sigma : Equiv.Perm (Fin m)) (f : (Fin m → F2) → ℝ) :
    ∑ x ∈ weightSlice m j, f (permuteAssignment sigma x) =
      ∑ x ∈ weightSlice m j, f x := by
  classical
  calc
    ∑ x ∈ weightSlice m j, f (permuteAssignment sigma x) =
        ∑ x : ↑(weightSlice m j),
          f (permuteAssignment sigma x.1) := by
      exact (Finset.sum_coe_sort (weightSlice m j)
        (fun x ↦ f (permuteAssignment sigma x))).symm
    _ = ∑ x : ↑(weightSlice m j), f x.1 := by
      exact Fintype.sum_equiv (weightSlicePermutationEquiv sigma j) _ _
        (fun _ ↦ rfl)
    _ = ∑ x ∈ weightSlice m j, f x := by
      exact Finset.sum_coe_sort (weightSlice m j) f

@[simp]
theorem evalBoolean_symmetrize {m : ℕ}
    (p : BooleanPolynomial m) (x : Fin m → F2) :
    evalBoolean x (symmetrize p) =
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
        ∑ sigma : Equiv.Perm (Fin m),
          evalBoolean (permuteAssignment sigma x) p := by
  simp [symmetrize, evalBoolean, permutePolynomial, permuteAssignment,
    MvPolynomial.eval_rename, Function.comp_def]

theorem sum_evalBoolean_symmetrize_weightSlice {m j : ℕ}
    (p : BooleanPolynomial m) :
    ∑ x ∈ weightSlice m j, evalBoolean x (symmetrize p) =
      ∑ x ∈ weightSlice m j, evalBoolean x p := by
  classical
  let n : ℝ := Fintype.card (Equiv.Perm (Fin m))
  have hn : n ≠ 0 := by
    unfold n
    have hpos : 0 < Fintype.card (Equiv.Perm (Fin m)) :=
      Fintype.card_pos_iff.mpr
        ⟨(Equiv.refl (Fin m) : Equiv.Perm (Fin m))⟩
    exact_mod_cast hpos.ne'
  calc
    ∑ x ∈ weightSlice m j, evalBoolean x (symmetrize p) =
        ∑ x ∈ weightSlice m j,
          n⁻¹ * ∑ sigma : Equiv.Perm (Fin m),
            evalBoolean (permuteAssignment sigma x) p := by
      simp only [evalBoolean_symmetrize, n]
    _ = n⁻¹ * ∑ x ∈ weightSlice m j,
          ∑ sigma : Equiv.Perm (Fin m),
            evalBoolean (permuteAssignment sigma x) p := by
      rw [Finset.mul_sum]
    _ = n⁻¹ * ∑ sigma : Equiv.Perm (Fin m),
          ∑ x ∈ weightSlice m j,
            evalBoolean (permuteAssignment sigma x) p := by
      congr 1
      rw [Finset.sum_comm]
    _ = n⁻¹ * ∑ _sigma : Equiv.Perm (Fin m),
          ∑ x ∈ weightSlice m j, evalBoolean x p := by
      congr 1
      apply Finset.sum_congr rfl
      intro sigma _
      exact sum_weightSlice_permuteAssignment sigma (fun x ↦ evalBoolean x p)
    _ = ∑ x ∈ weightSlice m j, evalBoolean x p := by
      simp [n, hn]

theorem booleanWeight_le {m : ℕ} (x : Fin m → F2) :
    booleanWeight x ≤ m := by
  unfold booleanWeight
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

theorem evalBoolean_symmetrize_eq_sliceAverage {m : ℕ}
    (p : BooleanPolynomial m) (x : Fin m → F2) :
    evalBoolean x (symmetrize p) = sliceAverage p (booleanWeight x) := by
  let s := weightSlice m (booleanWeight x)
  have hs : s.Nonempty := weightSlice_nonempty (booleanWeight_le x)
  have hcardNat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hcardNat
  have hsumConst :
      ∑ y ∈ s, evalBoolean y (symmetrize p) =
        (s.card : ℝ) * evalBoolean x (symmetrize p) := by
    calc
      ∑ y ∈ s, evalBoolean y (symmetrize p) =
          ∑ _y ∈ s, evalBoolean x (symmetrize p) := by
        apply Finset.sum_congr rfl
        intro y hy
        apply eval_symmetrize_depends_only_on_weight
        exact ((mem_weightSlice y).1 hy).trans rfl
      _ = (s.card : ℝ) * evalBoolean x (symmetrize p) := by simp
  calc
    evalBoolean x (symmetrize p) =
        (∑ y ∈ s, evalBoolean y (symmetrize p)) / (s.card : ℝ) := by
      rw [hsumConst]
      field_simp
    _ = (∑ y ∈ s, evalBoolean y p) / (s.card : ℝ) := by
      rw [sum_evalBoolean_symmetrize_weightSlice]
    _ = sliceAverage p (booleanWeight x) := rfl

/-! ## The binomial polynomial basis -/

/-- The falling-factorial polynomial divided by `s!`; at natural inputs it is `choose`. -/
noncomputable def choosePolynomial (s : ℕ) : Polynomial ℝ :=
  ((s.factorial : ℝ)⁻¹) • descPochhammer ℝ s

theorem natDegree_choosePolynomial_le (s : ℕ) :
    (choosePolynomial s).natDegree ≤ s := by
  exact (Polynomial.natDegree_smul_le _ _).trans_eq
    (descPochhammer_natDegree ℝ s)

@[simp]
theorem eval_choosePolynomial_nat (s j : ℕ) :
    (choosePolynomial s).eval (j : ℝ) = (j.choose s : ℝ) := by
  rw [choosePolynomial, Polynomial.eval_smul]
  change (s.factorial : ℝ)⁻¹ *
      (descPochhammer ℝ s).eval (j : ℝ) = (j.choose s : ℝ)
  rw [← div_eq_inv_mul]
  exact (Nat.cast_choose_eq_descPochhammer_div ℝ j s).symm

/-! ## Direct counting of multilinear monomials on a slice -/

theorem evalBoolean_monomial_eq_if_support_subset {m : ℕ}
    (exponent : Fin m →₀ ℕ) (coefficient : ℝ) (x : Fin m → F2) :
    evalBoolean x (MvPolynomial.monomial exponent coefficient) =
      if exponent.support ⊆ booleanSupport x then coefficient else 0 := by
  rw [evalBoolean, MvPolynomial.eval_monomial]
  by_cases hsubset : exponent.support ⊆ booleanSupport x
  · rw [if_pos hsubset]
    have hprod : exponent.prod (fun i e ↦ f2ToReal (x i) ^ e) = 1 := by
      rw [Finsupp.prod, Finset.prod_eq_one]
      intro i hi
      have hx : x i = 1 := (mem_booleanSupport x i).1 (hsubset hi)
      simp [hx]
    rw [hprod, mul_one]
  · rw [if_neg hsubset]
    obtain ⟨i, hi, hix⟩ := Finset.not_subset.mp hsubset
    have hx : x i = 0 := by
      rcases F2_eq_zero_or_one (x i) with hzero | hone
      · exact hzero
      · exact (hix ((mem_booleanSupport x i).2 hone)).elim
    have hexponent : exponent i ≠ 0 := Finsupp.mem_support_iff.mp hi
    rw [Finsupp.prod, Finset.prod_eq_zero hi]
    · simp
    · simp [hx, hexponent]

/-- Support equivalence restricted to assignments whose one-set contains `s`. -/
def containingSliceEquiv {m j : ℕ} (s : Finset (Fin m)) :
    ↑((weightSlice m j).filter fun x ↦ s ⊆ booleanSupport x) ≃
      ↑(((Finset.univ : Finset (Fin m)).powersetCard j).filter fun t ↦ s ⊆ t) where
  toFun x := ⟨booleanSupport x.1, by
    rw [Finset.mem_filter]
    have hx := (Finset.mem_filter.mp x.2)
    exact ⟨(Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by
        simpa [booleanWeight] using (mem_weightSlice x.1).1 hx.1⟩), hx.2⟩⟩
  invFun t := ⟨assignmentOfSupport t.1, by
    rw [Finset.mem_filter]
    have ht := Finset.mem_filter.mp t.2
    refine ⟨?_, ?_⟩
    · rw [mem_weightSlice, booleanWeight, booleanSupport_assignmentOfSupport]
      exact (Finset.mem_powersetCard.mp ht.1).2
    · simpa using ht.2⟩
  left_inv x := by
    apply Subtype.ext
    exact assignmentOfSupport_booleanSupport x.1
  right_inv t := by
    apply Subtype.ext
    exact booleanSupport_assignmentOfSupport t.1

theorem card_filter_weightSlice_support_subset {m j : ℕ}
    (s : Finset (Fin m)) (hsj : s.card ≤ j) :
    ((weightSlice m j).filter fun x ↦ s ⊆ booleanSupport x).card =
      (m - s.card).choose (j - s.card) := by
  calc
    ((weightSlice m j).filter fun x ↦ s ⊆ booleanSupport x).card =
        Fintype.card
          ↑((weightSlice m j).filter fun x ↦ s ⊆ booleanSupport x) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
          ↑(((Finset.univ : Finset (Fin m)).powersetCard j).filter
            fun t ↦ s ⊆ t) :=
      Fintype.card_congr (containingSliceEquiv s)
    _ = (((Finset.univ : Finset (Fin m)).powersetCard j).filter
            fun t ↦ s ⊆ t).card := Fintype.card_coe _
    _ = (m - s.card).choose (j - s.card) := by
      rw [Finset.card_filter_powersetCard_subset s Finset.univ j
        (Finset.subset_univ s) hsj]
      simp

theorem sum_evalBoolean_monomial_weightSlice {m j : ℕ}
    (exponent : Fin m →₀ ℕ) (coefficient : ℝ)
    (hsj : exponent.support.card ≤ j) :
    ∑ x ∈ weightSlice m j,
        evalBoolean x (MvPolynomial.monomial exponent coefficient) =
      coefficient *
        ((m - exponent.support.card).choose
          (j - exponent.support.card) : ℝ) := by
  calc
    ∑ x ∈ weightSlice m j,
        evalBoolean x (MvPolynomial.monomial exponent coefficient) =
        ∑ x ∈ weightSlice m j,
          if exponent.support ⊆ booleanSupport x then coefficient else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact evalBoolean_monomial_eq_if_support_subset exponent coefficient x
    _ = ∑ x ∈ (weightSlice m j).filter
          (fun x ↦ exponent.support ⊆ booleanSupport x), coefficient := by
      rw [Finset.sum_filter]
    _ = coefficient *
        ((m - exponent.support.card).choose
          (j - exponent.support.card) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_filter_weightSlice_support_subset exponent.support hsj]
      simp [mul_comm]

theorem sliceAverage_monomial {m j : ℕ}
    (exponent : Fin m →₀ ℕ) (coefficient : ℝ)
    (hj : j ≤ m) :
    sliceAverage (MvPolynomial.monomial exponent coefficient) j =
      coefficient * (j.choose exponent.support.card : ℝ) /
        (m.choose exponent.support.card : ℝ) := by
  have hsupportM : exponent.support.card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ exponent.support)
  have hmj : (m.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  have hms : (m.choose exponent.support.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hsupportM).ne'
  by_cases hsj : exponent.support.card ≤ j
  · unfold sliceAverage
    rw [sum_evalBoolean_monomial_weightSlice exponent coefficient hsj,
      card_weightSlice]
    have hchoose := Nat.choose_mul (n := m) (k := j)
      (s := exponent.support.card) hsj
    have hchooseReal :
        (m.choose j : ℝ) * (j.choose exponent.support.card : ℝ) =
          (m.choose exponent.support.card : ℝ) *
            ((m - exponent.support.card).choose
              (j - exponent.support.card) : ℝ) := by
      exact_mod_cast hchoose
    field_simp
    calc
      coefficient *
          ((m - exponent.support.card).choose
            (j - exponent.support.card) : ℝ) *
          (m.choose exponent.support.card : ℝ) =
          coefficient * ((m.choose exponent.support.card : ℝ) *
            ((m - exponent.support.card).choose
              (j - exponent.support.card) : ℝ)) := by ring
      _ = coefficient * ((m.choose j : ℝ) *
            (j.choose exponent.support.card : ℝ)) := by
        rw [← hchooseReal]
      _ = coefficient * (m.choose j : ℝ) *
            (j.choose exponent.support.card : ℝ) := by ring
  · have hzero :
        ∑ x ∈ weightSlice m j,
          evalBoolean x (MvPolynomial.monomial exponent coefficient) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [evalBoolean_monomial_eq_if_support_subset, if_neg]
      intro hsubset
      apply hsj
      calc
        exponent.support.card ≤ (booleanSupport x).card :=
          Finset.card_le_card hsubset
        _ = j := by
          exact (mem_weightSlice x).1 hx
    unfold sliceAverage
    rw [hzero, zero_div, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hsj)]
    simp

theorem sliceAverage_eq_sum_support {m j : ℕ}
    (p : BooleanPolynomial m) :
    sliceAverage p j =
      ∑ exponent ∈ p.support,
        sliceAverage
          (MvPolynomial.monomial exponent (p.coeff exponent)) j := by
  classical
  unfold sliceAverage
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ ↦ z / ((weightSlice m j).card : ℝ))
  calc
    ∑ x ∈ weightSlice m j, evalBoolean x p =
        ∑ x ∈ weightSlice m j,
          ∑ exponent ∈ p.support,
            evalBoolean x
              (MvPolynomial.monomial exponent (p.coeff exponent)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← evalBoolean_finset_sum]
      exact congrArg (evalBoolean x) (MvPolynomial.as_sum p)
    _ = ∑ exponent ∈ p.support,
          ∑ x ∈ weightSlice m j,
            evalBoolean x
              (MvPolynomial.monomial exponent (p.coeff exponent)) := by
      exact Finset.sum_comm

theorem exponent_sum_eq_support_card_of_apply_le_one {m : ℕ}
    (exponent : Fin m →₀ ℕ) (h : ∀ i, exponent i ≤ 1) :
    exponent.sum (fun _ e ↦ e) = exponent.support.card := by
  classical
  calc
    exponent.sum (fun _ e ↦ e) = ∑ i ∈ exponent.support, exponent i := rfl
    _ = ∑ _i ∈ exponent.support, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpos : 0 < exponent i := Nat.pos_of_ne_zero
        (Finsupp.mem_support_iff.mp hi)
      have hle := h i
      omega
    _ = exponent.support.card := by simp

theorem exponent_apply_le_one_of_multilinear {m : ℕ}
    {p : BooleanPolynomial m} (hp : p.Multilinear)
    {exponent : Fin m →₀ ℕ} (hexponent : exponent ∈ p.support)
    (i : Fin m) :
    exponent i ≤ 1 :=
  (MvPolynomial.monomial_le_degreeOf i hexponent).trans (hp i)

theorem exponent_sum_eq_support_card_of_multilinear {m : ℕ}
    {p : BooleanPolynomial m} (hp : p.Multilinear)
    {exponent : Fin m →₀ ℕ} (hexponent : exponent ∈ p.support) :
    exponent.sum (fun _ e ↦ e) = exponent.support.card :=
  exponent_sum_eq_support_card_of_apply_le_one exponent
    (exponent_apply_le_one_of_multilinear hp hexponent)

/-- Explicit binomial-basis polynomial representing all Boolean slice averages. -/
noncomputable def univariateSymmetrization {m : ℕ}
    (p : BooleanPolynomial m) : Polynomial ℝ :=
  ∑ exponent ∈ p.support,
    (p.coeff exponent /
      (m.choose (exponent.sum fun _ e ↦ e) : ℝ)) •
      choosePolynomial (exponent.sum fun _ e ↦ e)

theorem natDegree_univariateSymmetrization_le {m : ℕ}
    {p : BooleanPolynomial m} (_hp : p.Multilinear) :
    (univariateSymmetrization p).natDegree ≤ p.totalDegree := by
  classical
  unfold univariateSymmetrization
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((natDegree_choosePolynomial_le _).trans
      (MvPolynomial.le_totalDegree hexponent))

theorem eval_univariateSymmetrization {m : ℕ}
    {p : BooleanPolynomial m} (hp : p.Multilinear)
    (j : ℕ) (hj : j ≤ m) :
    (univariateSymmetrization p).eval (j : ℝ) = sliceAverage p j := by
  classical
  unfold univariateSymmetrization
  rw [Polynomial.eval_finsetSum, sliceAverage_eq_sum_support]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  rw [Polynomial.eval_smul, eval_choosePolynomial_nat,
    sliceAverage_monomial exponent (p.coeff exponent) hj]
  have hsum := exponent_sum_eq_support_card_of_multilinear hp hexponent
  rw [hsum]
  change (p.coeff exponent /
      (m.choose exponent.support.card : ℝ)) *
      (j.choose exponent.support.card : ℝ) =
    p.coeff exponent * (j.choose exponent.support.card : ℝ) /
      (m.choose exponent.support.card : ℝ)
  ring

theorem exists_univariate_symmetrization {m : ℕ}
    (p : BooleanPolynomial m) (hp : p.Multilinear) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ p.totalDegree ∧
        ∀ j : ℕ, j ≤ m → q.eval (j : ℝ) = sliceAverage p j := by
  exact ⟨univariateSymmetrization p,
    natDegree_univariateSymmetrization_le hp,
    eval_univariateSymmetrization hp⟩

/-! ## Transfer of OR approximation to the integer weight grid -/

theorem exists_univariate_of_multilinear_or_approximator {m d : ℕ}
    (p : BooleanPolynomial m) (hp : p.Multilinear)
    (hdegree : p.totalDegree ≤ d)
    (happrox : ∀ x : Fin m → F2,
      |evalBoolean x p - orValue x| ≤ (1 / 3 : ℝ)) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ d ∧
      |q.eval 0| ≤ (1 / 3 : ℝ) ∧
      ∀ j : ℕ, 0 < j → j ≤ m →
        |q.eval (j : ℝ) - 1| ≤ (1 / 3 : ℝ) := by
  refine ⟨univariateSymmetrization p,
    (natDegree_univariateSymmetrization_le hp).trans hdegree, ?_, ?_⟩
  · have heval : (univariateSymmetrization p).eval (0 : ℝ) =
        sliceAverage p 0 := by
      simpa using eval_univariateSymmetrization hp 0 (Nat.zero_le m)
    rw [heval]
    have havg := abs_sliceAverage_sub_le (p := p) (c := 0)
      (epsilon := (1 / 3 : ℝ)) (Nat.zero_le m) (fun x hx ↦ ?_)
    · simpa using havg
    · have hweight : booleanWeight x = 0 := (mem_weightSlice x).1 hx
      simpa [orValue_eq_zero_of_booleanWeight_eq_zero x hweight] using happrox x
  · intro j hjpos hjm
    rw [eval_univariateSymmetrization hp j hjm]
    apply abs_sliceAverage_sub_le hjm
    intro x hx
    have hweight : booleanWeight x = j := (mem_weightSlice x).1 hx
    have hweightPos : 0 < booleanWeight x := hweight.symm ▸ hjpos
    simpa [orValue_eq_one_of_booleanWeight_pos x hweightPos] using happrox x

theorem exists_univariate_of_or_approximator {m d : ℕ}
    (p : BooleanPolynomial m)
    (hdegree : p.totalDegree ≤ d)
    (happrox : ∀ x : Fin m → F2,
      |evalBoolean x p - orValue x| ≤ (1 / 3 : ℝ)) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ d ∧
      |q.eval 0| ≤ (1 / 3 : ℝ) ∧
      ∀ j : ℕ, 0 < j → j ≤ m →
        |q.eval (j : ℝ) - 1| ≤ (1 / 3 : ℝ) := by
  apply exists_univariate_of_multilinear_or_approximator (multilinearize p)
    (multilinear_multilinearize p)
    ((totalDegree_multilinearize_le p).trans hdegree)
  intro x
  simpa using happrox x

end ApproxDegree

end Revres
