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

/-- Reindex a certificate along equality of the represented functions. -/
noncomputable def congr {Q : (Fin N → F2) → ℝ}
    (cert : NSCertificate F P) (h : P = Q) : NSCertificate F Q where
  multiplier := cert.multiplier
  represents := by
    intro x
    rw [← h]
    exact cert.represents x

theorem congr_degreeLE {Q : (Fin N → F2) → ℝ}
    {cert : NSCertificate F P} {h : P = Q} {degree : ℕ}
    (hdegree : cert.DegreeLE degree) : (cert.congr h).DegreeLE degree :=
  hdegree

/-- Add two semantic certificates clausewise. -/
noncomputable def add {Q : (Fin N → F2) → ℝ}
    (certP : NSCertificate F P) (certQ : NSCertificate F Q) :
    NSCertificate F (P + Q) where
  multiplier C := certP.multiplier C + certQ.multiplier C
  represents := by
    intro x
    change P x + Q x = _
    rw [certP.represents x, certQ.represents x]
    unfold polynomialAxiomCombination
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _hC
    rw [add_mul, evalBoolean_add]

/-- Negate a semantic certificate clausewise. -/
noncomputable def neg (cert : NSCertificate F P) : NSCertificate F (-P) where
  multiplier C := -cert.multiplier C
  represents := by
    intro x
    change -P x = _
    rw [cert.represents x]
    unfold polynomialAxiomCombination
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro C _hC
    rw [neg_mul]
    simp [evalBoolean]

/-- Subtract two semantic certificates clausewise. -/
noncomputable def sub {Q : (Fin N → F2) → ℝ}
    (certP : NSCertificate F P) (certQ : NSCertificate F Q) :
    NSCertificate F (P - Q) where
  multiplier C := certP.multiplier C - certQ.multiplier C
  represents := by
    intro x
    change P x - Q x = _
    rw [certP.represents x, certQ.represents x]
    unfold polynomialAxiomCombination
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro C _hC
    rw [sub_mul, evalBoolean_sub]

theorem add_degree_le_max {Q : (Fin N → F2) → ℝ}
    {certP : NSCertificate F P} {certQ : NSCertificate F Q}
    {pDegree qDegree : ℕ} (hP : certP.DegreeLE pDegree)
    (hQ : certQ.DegreeLE qDegree) :
    (certP.add certQ).DegreeLE (max pDegree qDegree) := by
  rw [degree_le_iff]
  intro C hC
  rw [add, add_mul]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le_max ((degree_le_iff.mp hP) C hC) ((degree_le_iff.mp hQ) C hC))

theorem neg_degree_le {cert : NSCertificate F P} {degree : ℕ}
    (hcert : cert.DegreeLE degree) : cert.neg.DegreeLE degree := by
  rw [degree_le_iff]
  intro C hC
  rw [neg, neg_mul, MvPolynomial.totalDegree_neg]
  exact (degree_le_iff.mp hcert) C hC

theorem sub_degree_le_max {Q : (Fin N → F2) → ℝ}
    {certP : NSCertificate F P} {certQ : NSCertificate F Q}
    {pDegree qDegree : ℕ} (hP : certP.DegreeLE pDegree)
    (hQ : certQ.DegreeLE qDegree) :
    (certP.sub certQ).DegreeLE (max pDegree qDegree) := by
  rw [degree_le_iff]
  intro C hC
  rw [sub, sub_mul]
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le_max ((degree_le_iff.mp hP) C hC) ((degree_le_iff.mp hQ) C hC))

/-- Scale a semantic certificate by a real constant. -/
noncomputable def scale (a : ℝ) (cert : NSCertificate F P) :
    NSCertificate F (fun x ↦ a * P x) where
  multiplier C := a • cert.multiplier C
  represents := by
    intro x
    rw [cert.represents x]
    unfold polynomialAxiomCombination
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _hC
    rw [smul_mul_assoc]
    have heval :
        evalBoolean x (a • (cert.multiplier C * C.clausePolynomial)) =
          a * evalBoolean x (cert.multiplier C * C.clausePolynomial) := by
      simp [evalBoolean, MvPolynomial.smul_eval]
    rw [heval, evalBoolean_mul]

theorem scale_degreeLE (a : ℝ) {cert : NSCertificate F P} {degree : ℕ}
    (hcert : cert.DegreeLE degree) : (cert.scale a).DegreeLE degree := by
  rw [degree_le_iff]
  intro C hC
  rw [scale, smul_mul_assoc]
  exact (MvPolynomial.totalDegree_smul_le a _).trans
    ((degree_le_iff.mp hcert) C hC)

/-- Sum a finite family of semantic certificates. -/
noncomputable def finsetSum {index : Type*} (s : Finset index)
    (Q : index → (Fin N → F2) → ℝ)
    (cert : ∀ i, NSCertificate F (Q i)) :
    NSCertificate F (fun x ↦ ∑ i ∈ s, Q i x) where
  multiplier C := ∑ i ∈ s, (cert i).multiplier C
  represents := by
    intro x
    unfold polynomialAxiomCombination
    calc
      ∑ i ∈ s, Q i x =
          ∑ i ∈ s, ∑ C ∈ F,
            evalBoolean x ((cert i).multiplier C * C.clausePolynomial) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (cert i).represents x
      _ = ∑ C ∈ F, ∑ i ∈ s,
            evalBoolean x ((cert i).multiplier C * C.clausePolynomial) := by
        rw [Finset.sum_comm]
      _ = ∑ C ∈ F,
            evalBoolean x ((∑ i ∈ s, (cert i).multiplier C) * C.clausePolynomial) := by
        apply Finset.sum_congr rfl
        intro C _hC
        rw [Finset.sum_mul, evalBoolean_finset_sum]

theorem finsetSum_degree_le {index : Type*} {s : Finset index}
    {Q : index → (Fin N → F2) → ℝ}
    {cert : ∀ i, NSCertificate F (Q i)} {degree : ℕ}
    (hcert : ∀ i ∈ s, (cert i).DegreeLE degree) :
    (finsetSum s Q cert).DegreeLE degree := by
  rw [degree_le_iff]
  intro C hC
  rw [finsetSum, Finset.sum_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (degree_le_iff.mp (hcert i hi)) C hC

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

theorem hasCertificateDegreeLE_scale
    {F : CNF N} {P : (Fin N → F2) → ℝ} {degree : ℕ} (a : ℝ)
    (hcert : HasNSCertificateDegreeLE F P degree) :
    HasNSCertificateDegreeLE F (fun x ↦ a * P x) degree := by
  obtain ⟨cert, hdegree⟩ := hcert
  exact ⟨cert.scale a, NSCertificate.scale_degreeLE a hdegree⟩

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
