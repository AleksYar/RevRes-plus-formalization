import Revres.Polynomial.ClausePolynomial
import Revres.LowerBound.RobustIdentity

/-!
# Semantic Nullstellensatz certificates

Certificates are polynomial clause combinations whose equality to the represented function is
required pointwise on Boolean assignments. Their degree measures every complete
multiplier-times-clause product.
-/

namespace Revres

open Lemma53
open scoped BigOperators

variable {N : ℕ}

/-- Evaluate a family of polynomial multipliers against all clause polynomials in a CNF. -/
noncomputable def polynomialAxiomCombination
    (F : CNF N)
    (multiplier : Clause N → BooleanPolynomial N)
    (x : Fin N → F2) : ℝ :=
  ∑ C ∈ F, evalBoolean x (multiplier C * C.clausePolynomial)

/-- A semantic Nullstellensatz certificate on the Boolean cube. -/
structure NSCertificate
    (F : CNF N)
    (P : (Fin N → F2) → ℝ) where
  multiplier : Clause N → BooleanPolynomial N
  represents : ∀ x, P x = polynomialAxiomCombination F multiplier x

namespace NSCertificate

variable {F : CNF N} {P : (Fin N → F2) → ℝ}

theorem represents_expanded (cert : NSCertificate F P) (x : Fin N → F2) :
    P x = ∑ C ∈ F,
      evalBoolean x (cert.multiplier C) * C.realFalsifiedIndicator x := by
  calc
    P x = polynomialAxiomCombination F cert.multiplier x := cert.represents x
    _ = ∑ C ∈ F,
        evalBoolean x (cert.multiplier C) * C.realFalsifiedIndicator x := by
      apply Finset.sum_congr rfl
      intro C _
      rw [evalBoolean_mul, Clause.clausePolynomial_evalBoolean]

/-- The maximum total degree of a complete multiplier-times-clause-polynomial summand. -/
noncomputable def degree (cert : NSCertificate F P) : ℕ :=
  F.sup fun C ↦ (cert.multiplier C * C.clausePolynomial).totalDegree

/-- A certificate has proof degree at most `bound`. -/
def DegreeLE (cert : NSCertificate F P) (bound : ℕ) : Prop :=
  cert.degree ≤ bound

theorem degree_le_iff {cert : NSCertificate F P} {bound : ℕ} :
    cert.DegreeLE bound ↔
      ∀ C ∈ F,
        (cert.multiplier C * C.clausePolynomial).totalDegree ≤ bound := by
  exact Finset.sup_le_iff

/-- The semantic certificate induced by a real coefficient on each clause. -/
noncomputable def ofAxiomCoefficients
    (coeff : Clause N → ℝ)
    (hP : ∀ x, P x = axiomCombination F coeff x) :
    NSCertificate F P where
  multiplier := fun C ↦ MvPolynomial.C (coeff C)
  represents := by
    intro x
    rw [hP x]
    unfold axiomCombination polynomialAxiomCombination
    apply Finset.sum_congr rfl
    intro C _
    rw [evalBoolean_mul, evalBoolean_C, Clause.clausePolynomial_evalBoolean]

theorem ofAxiomCoefficients_degree_le
    (coeff : Clause N → ℝ)
    (hP : ∀ x, P x = axiomCombination F coeff x) :
    (ofAxiomCoefficients coeff hP).DegreeLE F.width := by
  rw [degree_le_iff]
  intro C hC
  calc
    ((ofAxiomCoefficients coeff hP).multiplier C * C.clausePolynomial).totalDegree ≤
        ((ofAxiomCoefficients coeff hP).multiplier C).totalDegree +
          C.clausePolynomial.totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = C.clausePolynomial.totalDegree := by
      simp [ofAxiomCoefficients]
    _ ≤ C.width := Clause.totalDegree_clausePolynomial_le C
    _ ≤ F.width := CNF.clause_width_le_width hC

end NSCertificate

/-- A function has a semantic Nullstellensatz certificate of proof degree at most `degree`. -/
def HasNSCertificateDegreeLE
    (F : CNF N)
    (P : (Fin N → F2) → ℝ)
    (degree : ℕ) : Prop :=
  ∃ cert : NSCertificate F P, cert.DegreeLE degree

/-- A nonnegative scalar combination of clause indicators is a constant-multiplier certificate
whose proof degree is at most the maximum clause width. -/
theorem hasCertificate_of_hasNonnegativeAxiomRepresentation
    {F : CNF N} {P : (Fin N → F2) → ℝ}
    (hP : HasNonnegativeAxiomRepresentation F P) :
    HasNSCertificateDegreeLE F P F.width := by
  obtain ⟨coeff, _hcoeff, hrepr⟩ := hP
  exact ⟨NSCertificate.ofAxiomCoefficients coeff hrepr,
    NSCertificate.ofAxiomCoefficients_degree_le coeff hrepr⟩

end Revres
