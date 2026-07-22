import Revres.SoPL.ApproxNS.ORReduction
import Revres.ApproxDegree.OR

/-!
# Support-local approximate Nullstellensatz hardness for SoPL

The support-local certificate reduction produces a low-degree OR approximator in the locality
regime. The explicit approximate-degree lower bound for OR then gives a quadratic certificate
degree bound; the complementary locality regime is immediate arithmetically.
-/

namespace Revres

open Lemma53

namespace SoPL

/-- The OR predicates used by the support-local reduction and the generic approximate-degree
layer are definitionally the same function. -/
@[simp]
theorem ApproxNS.orIndicator_eq_orValue {ell : ℕ} (x : ApproxNS.ORInput ell) :
    ApproxNS.orIndicator x = ApproxDegree.orValue x := by
  rfl

/-- The explicit constant in the support-local SoPL certificate-degree bound. -/
def C_sopl : ℕ := 8192

/-- A certificate approximating one on every encoded path family has degree quadratically large
in the number of non-planted paths. -/
theorem pathFamilyNS_degree_quadratic
    {ell : ℕ} (hell : 0 < ell)
    (Q : (Fin (Encoding.variableCount ell) → F2) → ℝ)
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (happrox : ∀ y, IsEncodedPathFamily ell hell y →
      (1 / 2 : ℝ) ≤ Q y ∧ Q y ≤ (3 / 2 : ℝ)) :
    BinaryPointer.order ell - 1 ≤
      C_sopl * (cert.degree + 1) ^ 2 := by
  by_cases hsmall :
      16 * cert.degree + ApproxNS.rowLocalitySlack < BinaryPointer.order ell
  · obtain ⟨p, hpDegree, hpApprox⟩ :=
      ApproxNS.exists_or_approximator_of_path_certificate
        hell cert happrox hsmall
    have hpApprox' : ∀ x : Fin (BinaryPointer.order ell - 1) → F2,
        |evalBoolean x p - ApproxDegree.orValue x| ≤ (1 / 3 : ℝ) := by
      intro x
      simpa using hpApprox x
    have hor := ApproxDegree.or_approx_degree_quadratic p hpApprox'
    have hbase : p.totalDegree + 1 ≤ 16 * (cert.degree + 1) := by
      omega
    have hsquare := Nat.pow_le_pow_left hbase 2
    have hscaled :
        ApproxDegree.C_or * (p.totalDegree + 1) ^ 2 ≤
          C_sopl * (cert.degree + 1) ^ 2 := by
      simp only [ApproxDegree.C_or, ApproxDegree.C_markov, C_sopl]
      nlinarith
    exact hor.trans hscaled
  · have horder : BinaryPointer.order ell ≤ 16 * cert.degree + 4 := by
      unfold ApproxNS.rowLocalitySlack at hsmall
      omega
    have harithmetic :
        16 * cert.degree + 3 ≤ C_sopl * (cert.degree + 1) ^ 2 := by
      unfold C_sopl
      nlinarith
    omega

/-- A sufficiently large path-family grid proves the existing support-local hardness interface. -/
theorem pathFamilyNSHardness_of_size
    {ell D : ℕ} (hell : 0 < ell)
    (hsize : C_sopl * D ^ 2 < BinaryPointer.order ell - 1) :
    PathFamilyNSHardness ell hell D := by
  intro Q cert happrox
  by_contra hdegree
  have hlt : cert.degree < D := by omega
  have hquadratic := pathFamilyNS_degree_quadratic hell Q cert happrox
  have hsucc : cert.degree + 1 ≤ D := by omega
  have hsquare := Nat.pow_le_pow_left hsucc 2
  have hscaled := Nat.mul_le_mul_left C_sopl hsquare
  omega

end SoPL

end Revres
