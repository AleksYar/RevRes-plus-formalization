import Revres.Polynomial.Certificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Error reduction for semantic Nullstellensatz certificates

The complete clause summands of a certificate form an ordinary polynomial. Multiplying every
certificate multiplier by `2` minus that polynomial realizes the error-squaring map
`z ↦ z * (2 - z)` without changing the underlying CNF.
-/

namespace Revres

open Lemma53
open scoped BigOperators

variable {N : ℕ}

/-- One exact error-squaring step around the target value `1`. -/
def squareErrorValue (z : ℝ) : ℝ :=
  z * (2 - z)

theorem squareErrorValue_eq (z : ℝ) :
    squareErrorValue z = 1 - (z - 1) ^ 2 := by
  unfold squareErrorValue
  ring

/-- Squaring the error around `1` sends radius `epsilon` to radius `epsilon ^ 2`. -/
theorem squareErrorValue_bounds {epsilon z : ℝ}
    (h : 1 - epsilon ≤ z ∧ z ≤ 1 + epsilon) :
    1 - epsilon ^ 2 ≤ squareErrorValue z ∧
      squareErrorValue z ≤ 1 := by
  have hleft : 0 ≤ epsilon - (z - 1) := by
    linarith [h.2]
  have hright : 0 ≤ epsilon + (z - 1) := by
    linarith [h.1]
  have hsquare : (z - 1) ^ 2 ≤ epsilon ^ 2 := by
    nlinarith [mul_nonneg hleft hright]
  rw [squareErrorValue_eq]
  constructor
  · linarith
  · nlinarith [sq_nonneg (z - 1)]

/-- Three exact error-squaring steps. -/
def reduceHalfErrorValue (z : ℝ) : ℝ :=
  squareErrorValue (squareErrorValue (squareErrorValue z))

/-- Three steps send `[1/2, 3/2]` through `[3/4, 1]` and `[15/16, 1]` to
`[255/256, 1]`. -/
theorem reduceHalfErrorValue_bounds {z : ℝ}
    (h : (1 / 2 : ℝ) ≤ z ∧ z ≤ (3 / 2 : ℝ)) :
    (255 / 256 : ℝ) ≤ reduceHalfErrorValue z ∧
      reduceHalfErrorValue z ≤ 1 := by
  have hinitial :
      1 - (1 / 2 : ℝ) ≤ z ∧ z ≤ 1 + (1 / 2 : ℝ) := by
    norm_num
    exact h
  have hfirstRaw := squareErrorValue_bounds
    (epsilon := (1 / 2 : ℝ)) (z := z) hinitial
  have hfirst :
      (3 / 4 : ℝ) ≤ squareErrorValue z ∧ squareErrorValue z ≤ 1 := by
    norm_num at hfirstRaw ⊢
    exact hfirstRaw
  have hsecondInput :
      1 - (1 / 4 : ℝ) ≤ squareErrorValue z ∧
        squareErrorValue z ≤ 1 + (1 / 4 : ℝ) := by
    constructor <;> norm_num <;> linarith [hfirst.1, hfirst.2]
  have hsecondRaw := squareErrorValue_bounds hsecondInput
  have hsecond :
      (15 / 16 : ℝ) ≤ squareErrorValue (squareErrorValue z) ∧
        squareErrorValue (squareErrorValue z) ≤ 1 := by
    norm_num at hsecondRaw ⊢
    exact hsecondRaw
  have hthirdInput :
      1 - (1 / 16 : ℝ) ≤ squareErrorValue (squareErrorValue z) ∧
        squareErrorValue (squareErrorValue z) ≤ 1 + (1 / 16 : ℝ) := by
    constructor <;> norm_num <;> linarith [hsecond.1, hsecond.2]
  have hthird := squareErrorValue_bounds hthirdInput
  norm_num [reduceHalfErrorValue] at hthird ⊢
  exact hthird

/-- The three-step endpoint restricted to an arbitrary support predicate. -/
theorem reduceHalfErrorValue_bounds_on
    (P : (Fin N → F2) → ℝ) (support : (Fin N → F2) → Prop)
    (happrox : ∀ x, support x →
      (1 / 2 : ℝ) ≤ P x ∧ P x ≤ (3 / 2 : ℝ)) :
    ∀ x, support x →
      (255 / 256 : ℝ) ≤ reduceHalfErrorValue (P x) ∧
        reduceHalfErrorValue (P x) ≤ 1 := by
  intro x hx
  exact reduceHalfErrorValue_bounds (happrox x hx)

namespace NSCertificate

variable {F : CNF N} {P : (Fin N → F2) → ℝ}

/-- The polynomial sum of all complete multiplier-times-clause summands. -/
noncomputable def combinationPolynomial (cert : NSCertificate F P) :
    BooleanPolynomial N :=
  ∑ C ∈ F, cert.multiplier C * C.clausePolynomial

@[simp]
theorem evalBoolean_combinationPolynomial
    (cert : NSCertificate F P) (x : Fin N → F2) :
    evalBoolean x cert.combinationPolynomial = P x := by
  rw [combinationPolynomial, evalBoolean_finset_sum]
  exact (cert.represents x).symm

/-- Summing the complete certificate terms cannot increase their maximum degree. -/
theorem totalDegree_combinationPolynomial_le (cert : NSCertificate F P) :
    cert.combinationPolynomial.totalDegree ≤ cert.degree := by
  unfold combinationPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro C hC
  exact (degree_le_iff.mp (show cert.DegreeLE cert.degree from le_rfl)) C hC

theorem totalDegree_combinationPolynomial_le_of_degreeLE
    {cert : NSCertificate F P} {degree : ℕ} (hdegree : cert.DegreeLE degree) :
    cert.combinationPolynomial.totalDegree ≤ degree :=
  cert.totalDegree_combinationPolynomial_le.trans hdegree

/-- Multiply every multiplier by `2` minus the full certificate polynomial. -/
noncomputable def squareError (cert : NSCertificate F P) :
    NSCertificate F (fun x => squareErrorValue (P x)) where
  multiplier C :=
    cert.multiplier C *
      ((2 : BooleanPolynomial N) - cert.combinationPolynomial)
  represents := by
    intro x
    rw [squareErrorValue, cert.represents x]
    unfold polynomialAxiomCombination
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro C _hC
    simp only [evalBoolean_mul, evalBoolean_sub,
      evalBoolean_combinationPolynomial]
    norm_num [evalBoolean]
    rw [cert.represents x]
    simp only [polynomialAxiomCombination, evalBoolean_mul]
    simp only [evalBoolean]
    ring

theorem squareError_degreeLE
    {cert : NSCertificate F P} {degree : ℕ}
    (hdegree : cert.DegreeLE degree) :
    cert.squareError.DegreeLE (2 * degree) := by
  have hcombination : cert.combinationPolynomial.totalDegree ≤ degree :=
    cert.totalDegree_combinationPolynomial_le_of_degreeLE hdegree
  have hfactor :
      ((2 : BooleanPolynomial N) - cert.combinationPolynomial).totalDegree ≤
        degree := by
    calc
      ((2 : BooleanPolynomial N) - cert.combinationPolynomial).totalDegree ≤
          max (2 : BooleanPolynomial N).totalDegree
            cert.combinationPolynomial.totalDegree :=
        MvPolynomial.totalDegree_sub _ _
      _ ≤ max 0 degree := max_le_max (by
        change (MvPolynomial.C (2 : ℝ) : BooleanPolynomial N).totalDegree ≤ 0
        rw [MvPolynomial.totalDegree_C]) hcombination
      _ = degree := by simp
  rw [degree_le_iff]
  intro C hC
  change
    ((cert.multiplier C *
          ((2 : BooleanPolynomial N) - cert.combinationPolynomial)) *
        C.clausePolynomial).totalDegree ≤ 2 * degree
  calc
    ((cert.multiplier C *
          ((2 : BooleanPolynomial N) - cert.combinationPolynomial)) *
        C.clausePolynomial).totalDegree =
        ((cert.multiplier C * C.clausePolynomial) *
          ((2 : BooleanPolynomial N) - cert.combinationPolynomial)).totalDegree := by
      congr 1
      ring
    _ ≤ (cert.multiplier C * C.clausePolynomial).totalDegree +
          ((2 : BooleanPolynomial N) - cert.combinationPolynomial).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ degree + degree :=
      Nat.add_le_add ((degree_le_iff.mp hdegree) C hC) hfactor
    _ = 2 * degree := by omega

/-- Apply the explicit certificate error-squaring operation exactly three times. -/
noncomputable def reduceHalfError (cert : NSCertificate F P) :
    NSCertificate F (fun x => reduceHalfErrorValue (P x)) :=
  (cert.squareError.squareError.squareError).congr (by
    funext x
    rfl)

theorem reduceHalfError_degreeLE
    {cert : NSCertificate F P} {degree : ℕ}
    (hdegree : cert.DegreeLE degree) :
    cert.reduceHalfError.DegreeLE (8 * degree) := by
  unfold reduceHalfError
  apply congr_degreeLE
  have hfirst := squareError_degreeLE hdegree
  have hsecond := squareError_degreeLE hfirst
  have hthird := squareError_degreeLE hsecond
  convert hthird using 1
  all_goals omega

end NSCertificate

end Revres
