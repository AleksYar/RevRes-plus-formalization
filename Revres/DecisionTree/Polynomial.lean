import Revres.DecisionTree.Basic
import Revres.Polynomial.Substitution

/-!
# Polynomial representations of Boolean decision trees

Each branch polynomial is specialized at the bit selected by its parent query before multiplication
by the corresponding literal. This makes the resulting ordinary real polynomial syntactically
multilinear even when a tree queries the same variable repeatedly along a path.
-/

namespace Revres

open Lemma53

variable {N : ℕ}

namespace BooleanPolynomial

/-- Every variable occurs with individual degree at most one. -/
def Multilinear (p : BooleanPolynomial N) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

namespace Multilinear

theorem C (r : ℝ) :
    Multilinear (MvPolynomial.C r : BooleanPolynomial N) := by
  intro i
  simp

theorem add {p q : BooleanPolynomial N}
    (hp : p.Multilinear) (hq : q.Multilinear) :
    (p + q).Multilinear := by
  intro i
  exact (MvPolynomial.degreeOf_add_le i p q).trans (max_le (hp i) (hq i))

theorem fixVariables {p : BooleanPolynomial N}
    (hp : p.Multilinear) (rho : Fin N → Option F2) :
    (BooleanPolynomial.fixVariables rho p).Multilinear := by
  intro i
  exact (BooleanPolynomial.degreeOf_fixVariables_le rho p i).trans (hp i)

theorem mul_of_disjoint_vars {p q : BooleanPolynomial N}
    (hp : p.Multilinear) (hq : q.Multilinear)
    (hdisjoint : Disjoint p.vars q.vars) :
    (p * q).Multilinear := by
  intro i
  refine (MvPolynomial.degreeOf_mul_le i p q).trans ?_
  by_cases hip : i ∈ p.vars
  · have hiq : i ∉ q.vars := by
      exact fun hiqmem ↦ Finset.disjoint_left.mp hdisjoint hip hiqmem
    have hqzero : q.degreeOf i = 0 := by
      by_contra hne
      exact hiq (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hne)
    simpa [hqzero] using hp i
  · have hpzero : p.degreeOf i = 0 := by
      by_contra hne
      exact hip (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hne)
    simpa [hpzero] using hq i

end Multilinear

end BooleanPolynomial

namespace Clause

theorem vars_literalPolynomial (i : Fin N) (b : F2) :
    (literalPolynomial i b).vars = {i} := by
  rcases F2_eq_zero_or_one b with rfl | rfl
  · have hdisjoint :
        Disjoint (1 : BooleanPolynomial N).vars
          (MvPolynomial.X i : BooleanPolynomial N).vars := by
      simp
    simp only [literalPolynomial, zero_ne_one, if_false]
    rw [MvPolynomial.vars_sub_of_disjoint (1 : BooleanPolynomial N) hdisjoint]
    simp
  · simp [literalPolynomial]

theorem multilinear_literalPolynomial (i : Fin N) (b : F2) :
    (literalPolynomial i b).Multilinear := by
  intro j
  exact (MvPolynomial.degreeOf_le_totalDegree (literalPolynomial i b) j).trans_eq
    (totalDegree_literalPolynomial_eq i b)

end Clause

namespace DecisionTree

variable {α : Type*}

/-- The partial assignment fixing exactly one queried variable. -/
def branchAssignment (i : Fin N) (b : F2) : Fin N → Option F2 :=
  fun j ↦ if j = i then some b else none

@[simp]
theorem branchAssignment_self (i : Fin N) (b : F2) :
    branchAssignment i b i = some b := by
  simp [branchAssignment]

@[simp]
theorem branchAssignment_of_ne {i j : Fin N} (b : F2) (hji : j ≠ i) :
    branchAssignment i b j = none := by
  simp [branchAssignment, hji]

theorem fillAssignment_branchAssignment_eq
    (i : Fin N) (b : F2) (x : Fin N → F2) (hxi : x i = b) :
    BooleanPolynomial.fillAssignment (branchAssignment i b) x = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [hxi]
  · simp [branchAssignment_of_ne b hji]

theorem not_mem_vars_fixVariables_branchAssignment
    (i : Fin N) (b : F2) (p : BooleanPolynomial N) :
    i ∉ (BooleanPolynomial.fixVariables (branchAssignment i b) p).vars :=
  BooleanPolynomial.not_mem_vars_fixVariables_of_eq_some (branchAssignment_self i b)

/-- The multilinear polynomial represented by a real weighting of the tree's leaf values. -/
noncomputable def polynomial (encode : α → ℝ) :
    DecisionTree N α → BooleanPolynomial N
  | .leaf a => MvPolynomial.C (encode a)
  | .query i zeroTree oneTree =>
      Clause.literalPolynomial i 0 *
          BooleanPolynomial.fixVariables (branchAssignment i 0)
            (zeroTree.polynomial encode) +
        Clause.literalPolynomial i 1 *
          BooleanPolynomial.fixVariables (branchAssignment i 1)
            (oneTree.polynomial encode)

@[simp]
theorem polynomial_leaf (encode : α → ℝ) (a : α) :
    (leaf a : DecisionTree N α).polynomial encode = MvPolynomial.C (encode a) :=
  rfl

@[simp]
theorem polynomial_query (encode : α → ℝ) (i : Fin N)
    (zeroTree oneTree : DecisionTree N α) :
    (query i zeroTree oneTree).polynomial encode =
      Clause.literalPolynomial i 0 *
          BooleanPolynomial.fixVariables (branchAssignment i 0)
            (zeroTree.polynomial encode) +
        Clause.literalPolynomial i 1 *
          BooleanPolynomial.fixVariables (branchAssignment i 1)
            (oneTree.polynomial encode) :=
  rfl

@[simp]
theorem evalBoolean_polynomial
    (T : DecisionTree N α) (encode : α → ℝ) (x : Fin N → F2) :
    evalBoolean x (T.polynomial encode) = encode (T.eval x) := by
  induction T with
  | leaf a => simp
  | query i zeroTree oneTree ihzero ihone =>
      rcases F2_eq_zero_or_one (x i) with hi | hi
      · simp [polynomial, eval, hi, BooleanPolynomial.evalBoolean_fixVariables,
          fillAssignment_branchAssignment_eq, ihzero]
      · simp [polynomial, eval, hi, BooleanPolynomial.evalBoolean_fixVariables,
          fillAssignment_branchAssignment_eq, ihone]

theorem multilinear_polynomial
    (T : DecisionTree N α) (encode : α → ℝ) :
    (T.polynomial encode).Multilinear := by
  induction T with
  | leaf a => exact BooleanPolynomial.Multilinear.C (encode a)
  | query i zeroTree oneTree ihzero ihone =>
      apply BooleanPolynomial.Multilinear.add
      · apply BooleanPolynomial.Multilinear.mul_of_disjoint_vars
        · exact Clause.multilinear_literalPolynomial i 0
        · exact ihzero.fixVariables (branchAssignment i 0)
        · rw [Clause.vars_literalPolynomial, Finset.disjoint_singleton_left]
          exact not_mem_vars_fixVariables_branchAssignment i 0 _
      · apply BooleanPolynomial.Multilinear.mul_of_disjoint_vars
        · exact Clause.multilinear_literalPolynomial i 1
        · exact ihone.fixVariables (branchAssignment i 1)
        · rw [Clause.vars_literalPolynomial, Finset.disjoint_singleton_left]
          exact not_mem_vars_fixVariables_branchAssignment i 1 _

theorem totalDegree_polynomial_le_depth
    (T : DecisionTree N α) (encode : α → ℝ) :
    (T.polynomial encode).totalDegree ≤ T.depth := by
  induction T with
  | leaf a => simp
  | query i zeroTree oneTree ihzero ihone =>
      simp only [polynomial, depth]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · calc
          (Clause.literalPolynomial i 0 *
              BooleanPolynomial.fixVariables (branchAssignment i 0)
                (zeroTree.polynomial encode)).totalDegree ≤
              (Clause.literalPolynomial i 0).totalDegree +
                (BooleanPolynomial.fixVariables (branchAssignment i 0)
                  (zeroTree.polynomial encode)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ ≤ 1 + (zeroTree.polynomial encode).totalDegree := by
            rw [Clause.totalDegree_literalPolynomial_eq]
            exact Nat.add_le_add_left
              (BooleanPolynomial.totalDegree_fixVariables_le _ _) 1
          _ ≤ 1 + max zeroTree.depth oneTree.depth :=
            Nat.add_le_add_left (ihzero.trans (Nat.le_max_left _ _)) 1
      · calc
          (Clause.literalPolynomial i 1 *
              BooleanPolynomial.fixVariables (branchAssignment i 1)
                (oneTree.polynomial encode)).totalDegree ≤
              (Clause.literalPolynomial i 1).totalDegree +
                (BooleanPolynomial.fixVariables (branchAssignment i 1)
                  (oneTree.polynomial encode)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ ≤ 1 + (oneTree.polynomial encode).totalDegree := by
            rw [Clause.totalDegree_literalPolynomial_eq]
            exact Nat.add_le_add_left
              (BooleanPolynomial.totalDegree_fixVariables_le _ _) 1
          _ ≤ 1 + max zeroTree.depth oneTree.depth :=
            Nat.add_le_add_left (ihone.trans (Nat.le_max_right _ _)) 1

theorem exists_multilinear_polynomial_representation
    (T : DecisionTree N α) (encode : α → ℝ) :
    ∃ p : BooleanPolynomial N,
      p.Multilinear ∧ p.totalDegree ≤ T.depth ∧
        ∀ x, evalBoolean x p = encode (T.eval x) :=
  ⟨T.polynomial encode, T.multilinear_polynomial encode,
    T.totalDegree_polynomial_le_depth encode, T.evalBoolean_polynomial encode⟩

end DecisionTree

/-- Embed a Boolean truth value as `0` or `1` in the reals. -/
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0

@[simp]
theorem boolToReal_false : boolToReal false = 0 :=
  rfl

@[simp]
theorem boolToReal_true : boolToReal true = 1 :=
  rfl

namespace DecisionTree

/-- The `0/1` polynomial represented by a Boolean-output decision tree. -/
noncomputable def boolPolynomial (T : DecisionTree N Bool) : BooleanPolynomial N :=
  T.polynomial boolToReal

@[simp]
theorem evalBoolean_boolPolynomial
    (T : DecisionTree N Bool) (x : Fin N → F2) :
    evalBoolean x T.boolPolynomial = if T.eval x then 1 else 0 := by
  simp [boolPolynomial, boolToReal]

theorem multilinear_boolPolynomial (T : DecisionTree N Bool) :
    T.boolPolynomial.Multilinear :=
  T.multilinear_polynomial boolToReal

theorem totalDegree_boolPolynomial_le_depth (T : DecisionTree N Bool) :
    T.boolPolynomial.totalDegree ≤ T.depth :=
  T.totalDegree_polynomial_le_depth boolToReal

end DecisionTree

end Revres
