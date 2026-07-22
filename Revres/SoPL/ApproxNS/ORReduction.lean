import Revres.SoPL.ApproxNS.LocalIndistinguishability

/-!
# Extracting an OR approximating polynomial

Three error-squaring steps sharpen a support-local approximate certificate.  In the explicit
small-degree regime, local indistinguishability transfers the ideal solution-count intervals to
the actual polynomial.  The final map `r ↦ 1 - r ^ 2` then approximates OR with error at most
`1 / 3` and doubles the transformed degree.
-/

namespace Revres

open Lemma53

namespace SoPL

namespace ApproxNS

/-- The real indicator that at least one OR input coordinate is one. -/
def orIndicator {ell : ℕ} (x : ORInput ell) : ℝ :=
  if hammingWeight x = 0 then 0 else 1

@[simp]
theorem orIndicator_eq_zero_of_hammingWeight_eq_zero
    {ell : ℕ} (x : ORInput ell) (hzero : hammingWeight x = 0) :
    orIndicator x = 0 := by
  simp [orIndicator, hzero]

@[simp]
theorem orIndicator_eq_one_of_hammingWeight_pos
    {ell : ℕ} (x : ORInput ell) (hpos : 0 < hammingWeight x) :
    orIndicator x = 1 := by
  simp [orIndicator, Nat.ne_of_gt hpos]

/-- Error-reduce the certificate, form its actual polynomial, and square away from one. -/
noncomputable def orApproximator
    {ell : ℕ} (hell : 0 < ell)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q) :
    BooleanPolynomial (BinaryPointer.order ell - 1) :=
  1 - (actualPolynomial hell cert.reduceHalfError) ^ 2

@[simp]
theorem evalBoolean_orApproximator
    {ell : ℕ} (hell : 0 < ell)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (x : ORInput ell) :
    evalBoolean x (orApproximator hell cert) =
      1 - (evalBoolean x
        (actualPolynomial hell cert.reduceHalfError)) ^ 2 := by
  simp [orApproximator, evalBoolean]

theorem totalDegree_orApproximator_le
    {ell degree : ℕ} (hell : 0 < ell)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (hdegree : cert.DegreeLE degree) :
    (orApproximator hell cert).totalDegree ≤ 16 * degree := by
  have hsharp : cert.reduceHalfError.DegreeLE (8 * degree) :=
    NSCertificate.reduceHalfError_degreeLE hdegree
  have hactual :
      (actualPolynomial hell cert.reduceHalfError).totalDegree ≤ 8 * degree :=
    totalDegree_actualPolynomial_le cert.reduceHalfError hsharp
  unfold orApproximator
  calc
    (1 - (actualPolynomial hell cert.reduceHalfError) ^ 2).totalDegree ≤
        max (1 : BooleanPolynomial (BinaryPointer.order ell - 1)).totalDegree
          ((actualPolynomial hell cert.reduceHalfError) ^ 2).totalDegree :=
      MvPolynomial.totalDegree_sub _ _
    _ = ((actualPolynomial hell cert.reduceHalfError) ^ 2).totalDegree := by
      simp
    _ ≤ 2 * (actualPolynomial hell cert.reduceHalfError).totalDegree :=
      MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * (8 * degree) := Nat.mul_le_mul_left 2 hactual
    _ = 16 * degree := by omega

theorem actualPolynomial_bounds_of_hammingWeight_eq_zero
    {ell degree : ℕ} (hell : 0 < ell)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (hdegree : cert.DegreeLE degree)
    (happrox : ∀ y, IsEncodedPathFamily ell hell y →
      (1 / 2 : ℝ) ≤ Q y ∧ Q y ≤ (3 / 2 : ℝ))
    (hsmall :
      16 * degree + rowLocalitySlack < BinaryPointer.order ell)
    (x : ORInput ell) (hzero : hammingWeight x = 0) :
    (255 / 256 : ℝ) ≤
        evalBoolean x (actualPolynomial hell cert.reduceHalfError) ∧
      evalBoolean x (actualPolynomial hell cert.reduceHalfError) ≤ 1 := by
  obtain ⟨hsharpDegree, hsharp⟩ :=
    reduceHalfError_path cert hdegree happrox
  have hlocal :
      2 * (8 * degree) + rowLocalitySlack < BinaryPointer.order ell := by
    omega
  rw [actual_eq_ideal hell cert.reduceHalfError hsharpDegree hlocal x]
  exact idealValue_bounds_of_hammingWeight_eq_zero
    hell cert.reduceHalfError hsharp x hzero

theorem actualPolynomial_bounds_of_hammingWeight_pos
    {ell degree : ℕ} (hell : 0 < ell)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (hdegree : cert.DegreeLE degree)
    (happrox : ∀ y, IsEncodedPathFamily ell hell y →
      (1 / 2 : ℝ) ≤ Q y ∧ Q y ≤ (3 / 2 : ℝ))
    (hsmall :
      16 * degree + rowLocalitySlack < BinaryPointer.order ell)
    (x : ORInput ell) (hpos : 0 < hammingWeight x) :
    0 ≤ evalBoolean x (actualPolynomial hell cert.reduceHalfError) ∧
      evalBoolean x (actualPolynomial hell cert.reduceHalfError) ≤
        (1 / 2 : ℝ) := by
  obtain ⟨hsharpDegree, hsharp⟩ :=
    reduceHalfError_path cert hdegree happrox
  have hlocal :
      2 * (8 * degree) + rowLocalitySlack < BinaryPointer.order ell := by
    omega
  rw [actual_eq_ideal hell cert.reduceHalfError hsharpDegree hlocal x]
  exact idealValue_bounds_of_hammingWeight_pos
    hell cert.reduceHalfError hsharp x hpos

theorem one_sub_sq_approx_zero
    {r : ℝ}
    (hlower : (255 / 256 : ℝ) ≤ r)
    (hupper : r ≤ 1) :
    |(1 - r ^ 2) - 0| ≤ (1 / 3 : ℝ) := by
  have hrnonneg : 0 ≤ r := by
    norm_num at hlower ⊢
    linarith
  have hsquareLower : (255 / 256 : ℝ) ^ 2 ≤ r ^ 2 := by
    have hproduct :
        0 ≤ (r - (255 / 256 : ℝ)) * (r + (255 / 256 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hlower) (by positivity)
    nlinarith
  have hsquareUpper : r ^ 2 ≤ 1 := by
    have hproduct : 0 ≤ (1 - r) * (1 + r) :=
      mul_nonneg (sub_nonneg.mpr hupper) (by linarith)
    nlinarith
  have hnonneg : 0 ≤ 1 - r ^ 2 := by linarith
  rw [sub_zero, abs_of_nonneg hnonneg]
  have hnumerical :
      (1 : ℝ) - (255 / 256 : ℝ) ^ 2 < 1 / 3 := by
    norm_num
  linarith

theorem one_sub_sq_approx_one
    {r : ℝ}
    (hlower : 0 ≤ r)
    (hupper : r ≤ (1 / 2 : ℝ)) :
    |(1 - r ^ 2) - 1| ≤ (1 / 3 : ℝ) := by
  have hsquareUpper : r ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hproduct : 0 ≤ ((1 / 2 : ℝ) - r) * ((1 / 2 : ℝ) + r) :=
      mul_nonneg (sub_nonneg.mpr hupper) (by linarith)
    nlinarith
  rw [show (1 - r ^ 2) - 1 = -(r ^ 2) by ring, abs_neg,
    abs_of_nonneg (sq_nonneg r)]
  have hnumerical : (1 / 2 : ℝ) ^ 2 < 1 / 3 := by norm_num
  linarith

theorem orApproximator_error
    {ell degree : ℕ} (hell : 0 < ell)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (hdegree : cert.DegreeLE degree)
    (happrox : ∀ y, IsEncodedPathFamily ell hell y →
      (1 / 2 : ℝ) ≤ Q y ∧ Q y ≤ (3 / 2 : ℝ))
    (hsmall :
      16 * degree + rowLocalitySlack < BinaryPointer.order ell)
    (x : ORInput ell) :
    |evalBoolean x (orApproximator hell cert) - orIndicator x| ≤
      (1 / 3 : ℝ) := by
  rw [evalBoolean_orApproximator]
  by_cases hzero : hammingWeight x = 0
  · rw [orIndicator_eq_zero_of_hammingWeight_eq_zero x hzero]
    have hbounds := actualPolynomial_bounds_of_hammingWeight_eq_zero
      hell cert hdegree happrox hsmall x hzero
    exact one_sub_sq_approx_zero hbounds.1 hbounds.2
  · have hpos : 0 < hammingWeight x := Nat.pos_of_ne_zero hzero
    rw [orIndicator_eq_one_of_hammingWeight_pos x hpos]
    have hbounds := actualPolynomial_bounds_of_hammingWeight_pos
      hell cert hdegree happrox hsmall x hpos
    exact one_sub_sq_approx_one hbounds.1 hbounds.2

theorem exists_or_approximator_of_path_certificate
    {ell : ℕ} (hell : 0 < ell)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (happrox : ∀ y, IsEncodedPathFamily ell hell y →
      (1 / 2 : ℝ) ≤ Q y ∧ Q y ≤ (3 / 2 : ℝ))
    (hsmall :
      16 * cert.degree + rowLocalitySlack < BinaryPointer.order ell) :
    ∃ p : BooleanPolynomial (BinaryPointer.order ell - 1),
      p.totalDegree ≤ 16 * cert.degree ∧
        ∀ x : ORInput ell,
          |evalBoolean x p - orIndicator x| ≤ (1 / 3 : ℝ) := by
  refine ⟨orApproximator hell cert,
    totalDegree_orApproximator_le hell cert le_rfl, ?_⟩
  intro x
  exact orApproximator_error hell cert le_rfl happrox hsmall x

end ApproxNS

end SoPL

end Revres
