import Revres.Polynomial.Certificate
import Revres.Polynomial.Substitution

/-!
# Normalized semantic Nullstellensatz certificates

Each multiplier is specialized at its clause's unique falsifying assignment. The resulting
multiplier avoids the clause variables, represents the same function on the Boolean cube, and does
not increase the full multiplier-times-clause proof degree.
-/

namespace Revres

open Lemma53

variable {N : ℕ}

namespace NSCertificate

variable {F : CNF N} {P : (Fin N → F2) → ℝ}

/-- Every formula multiplier avoids the variables already fixed by its clause. -/
def Normalized (cert : NSCertificate F P) : Prop :=
  ∀ ⦃C⦄, C ∈ F → Disjoint (cert.multiplier C).vars C.support

/-- Specialize every multiplier at the unique falsifying assignment of its clause. -/
noncomputable def normalize (cert : NSCertificate F P) : NSCertificate F P where
  multiplier := fun C ↦ BooleanPolynomial.fixVariables C (cert.multiplier C)
  represents := by
    intro x
    rw [cert.represents x]
    unfold polynomialAxiomCombination
    apply Finset.sum_congr rfl
    intro C _hC
    exact (Clause.evalBoolean_fixVariables_mul_clausePolynomial
      C (cert.multiplier C) x).symm

@[simp]
theorem normalize_multiplier (cert : NSCertificate F P) (C : Clause N) :
    cert.normalize.multiplier C =
      BooleanPolynomial.fixVariables C (cert.multiplier C) :=
  rfl

theorem normalize_normalized (cert : NSCertificate F P) :
    cert.normalize.Normalized := by
  intro C _hC
  rw [normalize_multiplier]
  exact Clause.disjoint_vars_fixVariables_support C (cert.multiplier C)

theorem normalize_degree_le (cert : NSCertificate F P) :
    cert.normalize.degree ≤ cert.degree := by
  change cert.normalize.DegreeLE cert.degree
  rw [degree_le_iff]
  intro C hC
  have horiginal :
      (cert.multiplier C * C.clausePolynomial).totalDegree ≤ cert.degree :=
    (degree_le_iff.mp (show cert.DegreeLE cert.degree from le_rfl)) C hC
  exact (Clause.totalDegree_fixVariables_mul_clausePolynomial_le
    C (cert.multiplier C)).trans horiginal

end NSCertificate

theorem normalize_certificate
    {F : CNF N} {P : (Fin N → F2) → ℝ}
    (cert : NSCertificate F P) :
    ∃ cert' : NSCertificate F P,
      cert'.Normalized ∧ cert'.degree ≤ cert.degree :=
  ⟨cert.normalize, cert.normalize_normalized, cert.normalize_degree_le⟩

theorem exists_normalized_certificate_of_degree_le
    {F : CNF N} {P : (Fin N → F2) → ℝ} {degree : ℕ}
    (h : HasNSCertificateDegreeLE F P degree) :
    ∃ cert : NSCertificate F P,
      cert.Normalized ∧ cert.DegreeLE degree := by
  obtain ⟨cert, hdegree⟩ := h
  exact ⟨cert.normalize, cert.normalize_normalized,
    cert.normalize_degree_le.trans hdegree⟩

end Revres
