import Revres.Polynomial.ClausePolynomial
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Boolean polynomial specialization

Variables specified by a partial Boolean assignment are replaced by their real Boolean constants.
This is ordinary polynomial substitution; equality with the original clause product is asserted
only after evaluation on the Boolean cube.
-/

namespace Revres

open Lemma53

variable {N : ℕ}

namespace BooleanPolynomial

/-- Complete a partial assignment by retaining the values of `x` at unspecified coordinates. -/
def fillAssignment
    (rho : Fin N → Option F2) (x : Fin N → F2) : Fin N → F2 :=
  fun i ↦ (rho i).getD (x i)

@[simp]
theorem fillAssignment_none
    {rho : Fin N → Option F2} {x : Fin N → F2} {i : Fin N}
    (hi : rho i = none) :
    fillAssignment rho x i = x i := by
  simp [fillAssignment, hi]

@[simp]
theorem fillAssignment_some
    {rho : Fin N → Option F2} {x : Fin N → F2} {i : Fin N} {b : F2}
    (hi : rho i = some b) :
    fillAssignment rho x i = b := by
  simp [fillAssignment, hi]

/-- Fix every variable specified by `rho` and leave every other variable formal. -/
noncomputable def fixVariables
    (rho : Fin N → Option F2) :
    BooleanPolynomial N →ₐ[ℝ] BooleanPolynomial N :=
  MvPolynomial.bind₁ fun i ↦
    match rho i with
    | none => MvPolynomial.X i
    | some b => MvPolynomial.C (f2ToReal b)

@[simp]
theorem fixVariables_C (rho : Fin N → Option F2) (r : ℝ) :
    fixVariables rho (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [fixVariables]

@[simp]
theorem fixVariables_X (rho : Fin N → Option F2) (i : Fin N) :
    fixVariables rho (MvPolynomial.X i) =
      match rho i with
      | none => MvPolynomial.X i
      | some b => MvPolynomial.C (f2ToReal b) := by
  simp [fixVariables]

theorem evalBoolean_fixVariables
    (rho : Fin N → Option F2) (x : Fin N → F2)
    (p : BooleanPolynomial N) :
    evalBoolean x (fixVariables rho p) =
      evalBoolean (fillAssignment rho x) p := by
  change
    MvPolynomial.aeval (fun i ↦ f2ToReal (x i))
        (MvPolynomial.bind₁
          (fun i ↦
            match rho i with
            | none => MvPolynomial.X i
            | some b => MvPolynomial.C (f2ToReal b)) p) =
      MvPolynomial.aeval (fun i ↦ f2ToReal (fillAssignment rho x i)) p
  rw [MvPolynomial.aeval_bind₁]
  apply congrArg (fun values : Fin N → ℝ ↦ MvPolynomial.aeval values p)
  funext i
  cases hi : rho i with
  | none => simp [fillAssignment, hi]
  | some b => simp [fillAssignment, hi]

theorem not_mem_vars_fixVariables_of_eq_some
    {rho : Fin N → Option F2} {p : BooleanPolynomial N}
    {i : Fin N} {b : F2} (hi : rho i = some b) :
    i ∉ (fixVariables rho p).vars := by
  classical
  intro himem
  obtain ⟨j, _hjp, hjvars⟩ :=
    MvPolynomial.mem_vars_bind₁
      (fun j ↦
        match rho j with
        | none => MvPolynomial.X j
        | some c => MvPolynomial.C (f2ToReal c))
      p (by simpa [fixVariables] using himem)
  cases hj : rho j with
  | none =>
      have hij : i = j := by simpa [hj] using hjvars
      subst j
      simp [hi] at hj
  | some c =>
      simp [hj] at hjvars

private theorem totalDegree_variableImage_le
    (rho : Fin N → Option F2) (i : Fin N) :
    (match rho i with
      | none => (MvPolynomial.X i : BooleanPolynomial N)
      | some b => MvPolynomial.C (f2ToReal b)).totalDegree ≤ 1 := by
  cases rho i <;> simp

private theorem degreeOf_variableImage_le
    (rho : Fin N → Option F2) (i j : Fin N) :
    (match rho i with
      | none => (MvPolynomial.X i : BooleanPolynomial N)
      | some b => MvPolynomial.C (f2ToReal b)).degreeOf j ≤
        if j = i then 1 else 0 := by
  cases rho i <;> simp [MvPolynomial.degreeOf_X]

theorem totalDegree_fixVariables_le
    (rho : Fin N → Option F2) (p : BooleanPolynomial N) :
    (fixVariables rho p).totalDegree ≤ p.totalDegree := by
  classical
  let image : Fin N → BooleanPolynomial N := fun i ↦
    match rho i with
    | none => MvPolynomial.X i
    | some b => MvPolynomial.C (f2ToReal b)
  change (MvPolynomial.bind₁ image p).totalDegree ≤ p.totalDegree
  have hsum :
      MvPolynomial.bind₁ image p =
        ∑ d ∈ p.support,
          MvPolynomial.bind₁ image (MvPolynomial.monomial d (p.coeff d)) := by
    rw [← map_sum, ← p.as_sum]
  rw [hsum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.bind₁_monomial]
  calc
    (MvPolynomial.C (p.coeff d) *
        ∏ i ∈ d.support, image i ^ d i).totalDegree ≤
        (∏ i ∈ d.support, image i ^ d i).totalDegree := by
      simpa using MvPolynomial.totalDegree_mul
        (MvPolynomial.C (p.coeff d)) (∏ i ∈ d.support, image i ^ d i)
    _ ≤ ∑ i ∈ d.support, (image i ^ d i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd d.support fun i ↦ image i ^ d i
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (MvPolynomial.totalDegree_pow (image i) (d i)).trans (by
        simpa [image] using
          Nat.mul_le_mul_left (d i) (totalDegree_variableImage_le rho i))
    _ = d.sum fun _ e ↦ e := rfl
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

theorem degreeOf_fixVariables_le
    (rho : Fin N → Option F2) (p : BooleanPolynomial N) (coord : Fin N) :
    (fixVariables rho p).degreeOf coord ≤ p.degreeOf coord := by
  classical
  let image : Fin N → BooleanPolynomial N := fun i ↦
    match rho i with
    | none => MvPolynomial.X i
    | some b => MvPolynomial.C (f2ToReal b)
  change (MvPolynomial.bind₁ image p).degreeOf coord ≤ p.degreeOf coord
  have hsum :
      MvPolynomial.bind₁ image p =
        ∑ d ∈ p.support,
          MvPolynomial.bind₁ image (MvPolynomial.monomial d (p.coeff d)) := by
    rw [← map_sum, ← p.as_sum]
  rw [hsum]
  refine (MvPolynomial.degreeOf_sum_le coord p.support
    (fun d ↦ MvPolynomial.bind₁ image (MvPolynomial.monomial d (p.coeff d)))).trans ?_
  apply Finset.sup_le
  intro d hd
  rw [MvPolynomial.bind₁_monomial]
  calc
    (MvPolynomial.C (p.coeff d) *
        ∏ i ∈ d.support, image i ^ d i).degreeOf coord ≤
        (∏ i ∈ d.support, image i ^ d i).degreeOf coord :=
      MvPolynomial.degreeOf_C_mul_le _ _ _
    _ ≤ ∑ i ∈ d.support, (image i ^ d i).degreeOf coord :=
      MvPolynomial.degreeOf_prod_le coord d.support fun i ↦ image i ^ d i
    _ ≤ ∑ i ∈ d.support, if i = coord then d i else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        (image i ^ d i).degreeOf coord ≤
            d i * (image i).degreeOf coord :=
          MvPolynomial.degreeOf_pow_le coord (image i) (d i)
        _ ≤ d i * (if coord = i then 1 else 0) := by
          exact Nat.mul_le_mul_left (d i) (by
            simpa [image] using degreeOf_variableImage_le rho i coord)
        _ = if i = coord then d i else 0 := by
          by_cases hiv : i = coord
          · subst i
            simp
          · have hvi : coord ≠ i := fun h ↦ hiv h.symm
            simp [hiv, hvi]
    _ = d coord := by
      by_cases hv : coord ∈ d.support
      · rw [Finset.sum_eq_single coord]
        · simp
        · intro i _hi hiv
          simp [hiv]
        · exact fun hnot ↦ (hnot hv).elim
      · have hdv : d coord = 0 := Finsupp.notMem_support_iff.mp hv
        simp [hv, hdv]
    _ ≤ p.degreeOf coord := MvPolynomial.le_degreeOf_of_mem_support coord hd

end BooleanPolynomial

namespace Clause

theorem disjoint_vars_fixVariables_support
    (C : Clause N) (p : BooleanPolynomial N) :
    Disjoint (BooleanPolynomial.fixVariables C p).vars C.support := by
  classical
  rw [Finset.disjoint_left]
  intro i hip hiC
  obtain ⟨b, hib⟩ := exists_eq_some_of_mem_support hiC
  exact BooleanPolynomial.not_mem_vars_fixVariables_of_eq_some hib hip

theorem evalBoolean_fixVariables_of_falsified
    {C : Clause N} {p : BooleanPolynomial N} {x : Fin N → F2}
    (hC : C.Falsified x) :
    evalBoolean x (BooleanPolynomial.fixVariables C p) = evalBoolean x p := by
  rw [BooleanPolynomial.evalBoolean_fixVariables]
  congr 2
  funext i
  cases hi : C i with
  | none => simp [BooleanPolynomial.fillAssignment, hi]
  | some b => simp [BooleanPolynomial.fillAssignment, hi, hC i b hi]

theorem evalBoolean_fixVariables_mul_clausePolynomial
    (C : Clause N) (p : BooleanPolynomial N) (x : Fin N → F2) :
    evalBoolean x
        (BooleanPolynomial.fixVariables C p * C.clausePolynomial) =
      evalBoolean x (p * C.clausePolynomial) := by
  by_cases hC : C.Falsified x
  · simp only [evalBoolean_mul]
    rw [evalBoolean_fixVariables_of_falsified hC]
  · rw [evalBoolean_mul, evalBoolean_mul,
      clausePolynomial_evalBoolean_eq_if, if_neg hC]
    simp

theorem totalDegree_fixVariables_mul_clausePolynomial_le
    (C : Clause N) (p : BooleanPolynomial N) :
    (BooleanPolynomial.fixVariables C p * C.clausePolynomial).totalDegree ≤
      (p * C.clausePolynomial).totalDegree := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hfix : BooleanPolynomial.fixVariables C p = 0
  · simp [hfix]
  rw [MvPolynomial.totalDegree_mul_of_isDomain hfix (clausePolynomial_ne_zero C),
    MvPolynomial.totalDegree_mul_of_isDomain hp (clausePolynomial_ne_zero C)]
  exact Nat.add_le_add_right (BooleanPolynomial.totalDegree_fixVariables_le C p) _

end Clause

end Revres
