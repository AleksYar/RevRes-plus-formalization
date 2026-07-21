import Revres.CNF.Formula
import Revres.Lift.Average
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.Push

/-!
# Boolean clause polynomials

Ordinary clauses are represented by their real falsification polynomials.  Polynomial equality is
used only after evaluation on Boolean assignments; no Boolean quotient ring is introduced.
-/

namespace Revres

open Lemma53
open scoped BigOperators

variable {N : ℕ}

noncomputable local instance clausePolynomialFalsifiedDecidable
    (C : Clause N) (x : Fin N → F2) : Decidable (C.Falsified x) :=
  Classical.propDecidable _

/-- The ordinary real value of an `F2` bit.  This is not a ring homomorphism. -/
def f2ToReal (b : F2) : ℝ :=
  (b.val : ℝ)

@[simp]
theorem f2ToReal_zero : f2ToReal 0 = 0 := by
  simp [f2ToReal]

@[simp]
theorem f2ToReal_one : f2ToReal 1 = 1 := by
  change (((1 : F2).val : ℕ) : ℝ) = 1
  rw [ZMod.val_one]
  norm_num

@[simp]
theorem f2ToReal_eq_zero_iff {b : F2} : f2ToReal b = 0 ↔ b = 0 := by
  rcases F2_eq_zero_or_one b with rfl | rfl <;> simp

@[simp]
theorem f2ToReal_eq_one_iff {b : F2} : f2ToReal b = 1 ↔ b = 1 := by
  rcases F2_eq_zero_or_one b with rfl | rfl <;> simp

/-- Real multivariate polynomials in `N` Boolean variables. -/
abbrev BooleanPolynomial (N : ℕ) := MvPolynomial (Fin N) ℝ

/-- Evaluate a real polynomial at the real `0/1` values of an `F2` assignment. -/
noncomputable def evalBoolean
    (x : Fin N → F2) (p : BooleanPolynomial N) : ℝ :=
  MvPolynomial.eval (fun i ↦ f2ToReal (x i)) p

@[simp]
theorem evalBoolean_zero (x : Fin N → F2) :
    evalBoolean x (0 : BooleanPolynomial N) = 0 := by
  simp [evalBoolean]

@[simp]
theorem evalBoolean_one (x : Fin N → F2) :
    evalBoolean x (1 : BooleanPolynomial N) = 1 := by
  simp [evalBoolean]

@[simp]
theorem evalBoolean_C (x : Fin N → F2) (r : ℝ) :
    evalBoolean x (MvPolynomial.C r : BooleanPolynomial N) = r := by
  simp [evalBoolean]

@[simp]
theorem evalBoolean_X (x : Fin N → F2) (i : Fin N) :
    evalBoolean x (MvPolynomial.X i : BooleanPolynomial N) = f2ToReal (x i) := by
  simp [evalBoolean]

@[simp]
theorem evalBoolean_add (x : Fin N → F2) (p q : BooleanPolynomial N) :
    evalBoolean x (p + q) = evalBoolean x p + evalBoolean x q := by
  simp [evalBoolean]

@[simp]
theorem evalBoolean_sub (x : Fin N → F2) (p q : BooleanPolynomial N) :
    evalBoolean x (p - q) = evalBoolean x p - evalBoolean x q := by
  simp [evalBoolean]

@[simp]
theorem evalBoolean_mul (x : Fin N → F2) (p q : BooleanPolynomial N) :
    evalBoolean x (p * q) = evalBoolean x p * evalBoolean x q := by
  simp [evalBoolean]

theorem evalBoolean_finset_prod {ι : Type*} (x : Fin N → F2)
    (s : Finset ι) (p : ι → BooleanPolynomial N) :
    evalBoolean x (∏ i ∈ s, p i) = ∏ i ∈ s, evalBoolean x (p i) := by
  simp [evalBoolean]

theorem evalBoolean_finset_sum {ι : Type*} (x : Fin N → F2)
    (s : Finset ι) (p : ι → BooleanPolynomial N) :
    evalBoolean x (∑ i ∈ s, p i) = ∑ i ∈ s, evalBoolean x (p i) := by
  simp [evalBoolean]

namespace Clause

/-- The polynomial which checks that variable `i` has the specified Boolean value `b`. -/
noncomputable def literalPolynomial (i : Fin N) (b : F2) : BooleanPolynomial N :=
  if b = 1 then MvPolynomial.X i else 1 - MvPolynomial.X i

@[simp]
theorem literalPolynomial_evalBoolean (i : Fin N) (b : F2) (x : Fin N → F2) :
    evalBoolean x (literalPolynomial i b) = if x i = b then 1 else 0 := by
  rcases F2_eq_zero_or_one b with rfl | rfl
  · rcases F2_eq_zero_or_one (x i) with hx | hx <;> simp [literalPolynomial, hx]
  · rcases F2_eq_zero_or_one (x i) with hx | hx <;> simp [literalPolynomial, hx]

/-- The product of literal polynomials for the unique falsifying assignment of a clause. -/
noncomputable def clausePolynomial (C : Clause N) : BooleanPolynomial N :=
  ∏ i ∈ C.support, literalPolynomial i ((C i).getD 0)

theorem exists_eq_some_of_mem_support {C : Clause N} {i : Fin N} (hi : i ∈ C.support) :
    ∃ b, C i = some b := by
  cases hCi : C i with
  | none => simp [hCi] at hi
  | some b => exact ⟨b, rfl⟩

theorem clausePolynomial_evalBoolean_eq_if (C : Clause N) (x : Fin N → F2) :
    evalBoolean x C.clausePolynomial = if C.Falsified x then 1 else 0 := by
  classical
  rw [clausePolynomial, evalBoolean_finset_prod]
  by_cases hC : C.Falsified x
  · rw [if_pos hC]
    apply Finset.prod_eq_one
    intro i hi
    obtain ⟨b, hCi⟩ := exists_eq_some_of_mem_support hi
    have hget : (C i).getD 0 = b := by simp [hCi]
    rw [literalPolynomial_evalBoolean, hget, if_pos (hC i b hCi)]
  · rw [if_neg hC]
    simp only [Falsified] at hC
    push Not at hC
    obtain ⟨i, b, hCi, hxi⟩ := hC
    have hi : i ∈ C.support := by simp [hCi]
    apply Finset.prod_eq_zero hi
    have hget : (C i).getD 0 = b := by simp [hCi]
    rw [literalPolynomial_evalBoolean, hget, if_neg hxi]

@[simp]
theorem clausePolynomial_evalBoolean (C : Clause N) (x : Fin N → F2) :
    evalBoolean x C.clausePolynomial = C.realFalsifiedIndicator x := by
  rw [clausePolynomial_evalBoolean_eq_if]
  simp [realFalsifiedIndicator]

theorem totalDegree_literalPolynomial_le (i : Fin N) (b : F2) :
    (literalPolynomial i b).totalDegree ≤ 1 := by
  rcases F2_eq_zero_or_one b with rfl | rfl
  · simpa [literalPolynomial] using
      (MvPolynomial.totalDegree_sub
        (1 : BooleanPolynomial N) (MvPolynomial.X i : BooleanPolynomial N))
  · simp [literalPolynomial]

theorem totalDegree_literalPolynomial_eq (i : Fin N) (b : F2) :
    (literalPolynomial i b).totalDegree = 1 := by
  rcases F2_eq_zero_or_one b with rfl | rfl
  · simpa [literalPolynomial, sub_eq_add_neg] using
      (MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt
        (p := -(MvPolynomial.X i : BooleanPolynomial N))
        (q := (1 : BooleanPolynomial N)) (by simp))
  · simp [literalPolynomial]

theorem literalPolynomial_ne_zero (i : Fin N) (b : F2) :
    literalPolynomial i b ≠ 0 := by
  intro hzero
  have heval := congrArg (evalBoolean (fun _ ↦ b)) hzero
  simp at heval

theorem totalDegree_clausePolynomial_le (C : Clause N) :
    C.clausePolynomial.totalDegree ≤ C.width := by
  calc
    C.clausePolynomial.totalDegree ≤
        ∑ i ∈ C.support, (literalPolynomial i ((C i).getD 0)).totalDegree := by
      exact MvPolynomial.totalDegree_finsetProd C.support
        (fun i ↦ literalPolynomial i ((C i).getD 0))
    _ ≤ ∑ _i ∈ C.support, 1 := by
      exact Finset.sum_le_sum fun i _ ↦ totalDegree_literalPolynomial_le i ((C i).getD 0)
    _ = C.width := by simp [width]

theorem clausePolynomial_ne_zero (C : Clause N) :
    C.clausePolynomial ≠ 0 := by
  classical
  rw [clausePolynomial, Finset.prod_ne_zero_iff]
  exact fun i _ ↦ literalPolynomial_ne_zero i ((C i).getD 0)

theorem totalDegree_clausePolynomial_eq (C : Clause N) :
    C.clausePolynomial.totalDegree = C.width := by
  classical
  unfold clausePolynomial width
  induction C.support using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi,
        MvPolynomial.totalDegree_mul_of_isDomain
          (literalPolynomial_ne_zero i ((C i).getD 0))
          (Finset.prod_ne_zero_iff.mpr
            (fun j _ ↦ literalPolynomial_ne_zero j ((C j).getD 0))),
        totalDegree_literalPolynomial_eq, ih, Finset.card_insert_of_notMem hi, Nat.add_comm]

end Clause

end Revres
