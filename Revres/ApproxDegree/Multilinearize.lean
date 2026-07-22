import Revres.DecisionTree.Polynomial

/-!
# Boolean multilinearization

Ordinary multivariate polynomials are multilinearized monomial by monomial by replacing every
positive exponent by one.  This is an evaluated identity on the Boolean cube, not an equality in
the polynomial ring or a quotient by Boolean relations.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace ApproxDegree

/-- Replace every positive exponent by one. -/
noncomputable def squarefreeExponent {N : ℕ}
    (exponent : Fin N →₀ ℕ) : Fin N →₀ ℕ :=
  exponent.mapRange (fun e ↦ if e = 0 then 0 else 1) (by simp)

@[simp]
theorem squarefreeExponent_apply {N : ℕ}
    (exponent : Fin N →₀ ℕ) (i : Fin N) :
    squarefreeExponent exponent i = if exponent i = 0 then 0 else 1 :=
  rfl

@[simp]
theorem support_squarefreeExponent {N : ℕ}
    (exponent : Fin N →₀ ℕ) :
    (squarefreeExponent exponent).support = exponent.support := by
  classical
  ext i
  simp [Finsupp.mem_support_iff]

theorem squarefreeExponent_sum_le {N : ℕ}
    (exponent : Fin N →₀ ℕ) :
    (squarefreeExponent exponent).sum (fun _ e ↦ e) ≤
      exponent.sum (fun _ e ↦ e) := by
  classical
  rw [Finsupp.sum, Finsupp.sum, support_squarefreeExponent]
  apply Finset.sum_le_sum
  intro i hi
  rw [squarefreeExponent_apply, if_neg (Finsupp.mem_support_iff.mp hi)]
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

theorem squarefreeExponent_apply_le_one {N : ℕ}
    (exponent : Fin N →₀ ℕ) (i : Fin N) :
    squarefreeExponent exponent i ≤ 1 := by
  rw [squarefreeExponent_apply]
  split <;> simp

theorem evalBoolean_monomial_squarefreeExponent {N : ℕ}
    (exponent : Fin N →₀ ℕ) (coefficient : ℝ)
    (x : Fin N → F2) :
    evalBoolean x (MvPolynomial.monomial
      (squarefreeExponent exponent) coefficient) =
      evalBoolean x (MvPolynomial.monomial exponent coefficient) := by
  classical
  simp only [evalBoolean, MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod, Finsupp.prod, support_squarefreeExponent]
  apply Finset.prod_congr rfl
  intro i hi
  have hexponent : exponent i ≠ 0 := Finsupp.mem_support_iff.mp hi
  rcases F2_eq_zero_or_one (x i) with hzero | hone
  · simp [hzero, squarefreeExponent_apply, hexponent]
  · simp [hone]

/-- Collapse every monomial exponent to its squarefree support. -/
noncomputable def multilinearize {N : ℕ}
    (p : BooleanPolynomial N) : BooleanPolynomial N :=
  ∑ exponent ∈ p.support,
    MvPolynomial.monomial (squarefreeExponent exponent) (p.coeff exponent)

@[simp]
theorem evalBoolean_multilinearize {N : ℕ}
    (p : BooleanPolynomial N) (x : Fin N → F2) :
    evalBoolean x (multilinearize p) = evalBoolean x p := by
  classical
  rw [multilinearize, evalBoolean_finset_sum]
  calc
    (∑ exponent ∈ p.support,
        evalBoolean x
          (MvPolynomial.monomial (squarefreeExponent exponent) (p.coeff exponent))) =
        ∑ exponent ∈ p.support,
          evalBoolean x (MvPolynomial.monomial exponent (p.coeff exponent)) := by
      apply Finset.sum_congr rfl
      intro exponent _hexponent
      exact evalBoolean_monomial_squarefreeExponent exponent (p.coeff exponent) x
    _ = evalBoolean x p := by
      rw [← evalBoolean_finset_sum]
      exact congrArg (evalBoolean x) (MvPolynomial.as_sum p).symm

theorem totalDegree_multilinearize_le {N : ℕ}
    (p : BooleanPolynomial N) :
    (multilinearize p).totalDegree ≤ p.totalDegree := by
  classical
  unfold multilinearize
  apply MvPolynomial.totalDegree_finsetSum_le
  intro exponent hexponent
  exact (MvPolynomial.totalDegree_monomial_le
    (squarefreeExponent exponent) (p.coeff exponent)).trans
      ((squarefreeExponent_sum_le exponent).trans
        (MvPolynomial.le_totalDegree hexponent))

theorem multilinear_multilinearize {N : ℕ}
    (p : BooleanPolynomial N) :
    (multilinearize p).Multilinear := by
  classical
  intro i
  unfold multilinearize
  refine (MvPolynomial.degreeOf_sum_le i p.support
    (fun exponent ↦ MvPolynomial.monomial
      (squarefreeExponent exponent) (p.coeff exponent))).trans ?_
  rw [Finset.sup_le_iff]
  intro exponent hexponent
  rw [MvPolynomial.degreeOf_monomial_eq _ _
    (MvPolynomial.mem_support_iff.mp hexponent)]
  exact squarefreeExponent_apply_le_one exponent i

end ApproxDegree

end Revres
