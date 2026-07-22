import Revres.SoD.Preprocess.Curiosity
import Revres.SoD.Preprocess.Witnessing

/-!
# Complete conical-junta preprocessing for Sink-of-DAG

The explicit junta is node-aligned, made exit-curious, and then filtered to remove every term that
already witnesses a canonical SoD clause. The removed terms are subtracted from the polynomial
side through a bounded-degree semantic Nullstellensatz certificate.
-/

namespace Revres

namespace JuntaRep

variable {ell : ℕ}

theorem nonWitnessingPart_nodeAligned
    (F : CNF (SoD.Encoding.variableCount (2 * ell)))
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (haligned : JR.NodeAligned) : (JR.nonWitnessingPart F).NodeAligned := by
  intro t ht
  exact haligned t (mem_support_nonWitnessingPart.mp ht).1

theorem nonWitnessingPart_exitCurious (hell : 0 < ell)
    (F : CNF (SoD.Encoding.variableCount (2 * ell)))
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (hcurious : JR.ExitCurious hell) : (JR.nonWitnessingPart F).ExitCurious hell := by
  intro t ht
  exact hcurious t (mem_support_nonWitnessingPart.mp ht).1

end JuntaRep

namespace SoD.Preprocess

variable {ell degree : ℕ}

/-- Exact junta-degree cost of node alignment followed by curiosity completion. -/
def cleaningDegree (ell degree : ℕ) : ℕ :=
  2 * (degree * (2 * ell))

/-- The canonical padded-ambient SoD formula cleaned in Phase XI. -/
noncomputable def cleaningFormula {ell : ℕ} (hell : 0 < ell) :
    CNF (SoD.Encoding.variableCount (2 * ell)) :=
  SoD.Encoding.searchCNF (2 * ell) (SoD.ActiveEdge.ambientWidth_pos hell)

/-- Proof degree after combining the original constant-multiplier certificate with removed terms. -/
def cleaningCertificateDegree (ell degree : ℕ) : ℕ :=
  max (2 * (2 * ell)) (cleaningDegree ell degree)

theorem cleaningFormula_width_le (hell : 0 < ell) :
    (cleaningFormula hell).width ≤ 2 * (2 * ell) := by
  simpa [cleaningFormula] using
    SoD.Encoding.searchCNF_width_le (2 * ell) (SoD.ActiveEdge.ambientWidth_pos hell)

/--
Paper correspondence: Section `sec:base-lb`, Lemma `lem:cleaning` in
`revres_xor_superpoly_lower_bound_restriction_notation.tex`.

Mathematical content: Node alignment, exit curiosity, and witness removal turn
the robust-identity junta into a pointwise dominated clean nonnegative junta,
while preserving the error and controlling both junta and certificate degree.

Used by: `Revres.sod_cleaningFormula_robustAmplification`.
-/
theorem preprocess
    (hell : 0 < ell)
    {P E :
      (Fin (SoD.Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (hP : HasNonnegativeAxiomRepresentation (cleaningFormula hell) P)
    (hnonnegative : JR.Nonnegative)
    (hdegree : JR.DegreeLE degree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z) :
    ∃ (P' :
        (Fin (SoD.Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ)
      (JR' : JuntaRep (SoD.Encoding.variableCount (2 * ell))),
      HasNSCertificateDegreeLE (cleaningFormula hell) P'
        (cleaningCertificateDegree ell degree) ∧
      (∀ z, P' z = 1 + JR'.eval z + E z) ∧
      JR'.Nonnegative ∧
      JR'.DegreeLE (cleaningDegree ell degree) ∧
      JR'.NodeAligned ∧
      JR'.ExitCurious hell ∧
      JR'.NonWitnessing (cleaningFormula hell) ∧
      (∀ z, 0 ≤ JR'.eval z ∧ JR'.eval z ≤ JR.eval z) := by
  let aligned : JuntaRep (SoD.Encoding.variableCount (2 * ell)) :=
    JR.nodeAlign (2 * ell)
  let curious : JuntaRep (SoD.Encoding.variableCount (2 * ell)) :=
    aligned.makeExitCurious hell
  let witness : JuntaRep (SoD.Encoding.variableCount (2 * ell)) :=
    curious.witnessingPart (cleaningFormula hell)
  let cleaned : JuntaRep (SoD.Encoding.variableCount (2 * ell)) :=
    curious.nonWitnessingPart (cleaningFormula hell)
  let P' : (Fin (SoD.Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ :=
    P - witness.eval
  have haligned_nonnegative : aligned.Nonnegative :=
    JuntaRep.nodeAlign_nonnegative hnonnegative
  have haligned_degree : aligned.DegreeLE (degree * (2 * ell)) :=
    JuntaRep.nodeAlign_degreeLE hdegree
  have haligned_structural : aligned.NodeAligned := by
    exact JuntaRep.nodeAlign_nodeAligned JR
  have haligned_eval : aligned.eval = JR.eval :=
    JuntaRep.eval_nodeAlign JR
  have hcurious_nonnegative : curious.Nonnegative :=
    JuntaRep.makeExitCurious_nonnegative hell haligned_nonnegative
  have hcurious_degree : curious.DegreeLE (cleaningDegree ell degree) := by
    change curious.DegreeLE (2 * (degree * (2 * ell)))
    exact JuntaRep.makeExitCurious_degreeLE hell haligned_structural haligned_degree
  have hcurious_aligned : curious.NodeAligned :=
    JuntaRep.makeExitCurious_nodeAligned hell haligned_structural
  have hcurious_structural : curious.ExitCurious hell :=
    JuntaRep.makeExitCurious_exitCurious hell haligned_structural
  have hcurious_eval : curious.eval = JR.eval :=
    (JuntaRep.eval_makeExitCurious hell aligned).trans haligned_eval
  have hcleaned_nonnegative : cleaned.Nonnegative :=
    JuntaRep.nonWitnessingPart_nonnegative hcurious_nonnegative
  have hcleaned_degree : cleaned.DegreeLE (cleaningDegree ell degree) :=
    JuntaRep.nonWitnessingPart_degreeLE hcurious_degree
  have hcleaned_aligned : cleaned.NodeAligned :=
    JuntaRep.nonWitnessingPart_nodeAligned (cleaningFormula hell) hcurious_aligned
  have hcleaned_curious : cleaned.ExitCurious hell :=
    JuntaRep.nonWitnessingPart_exitCurious hell (cleaningFormula hell) hcurious_structural
  have hcleaned_nonwitnessing : cleaned.NonWitnessing (cleaningFormula hell) :=
    JuntaRep.nonWitnessingPart_nonWitnessing (cleaningFormula hell) curious
  obtain ⟨certP, hcertP⟩ := hasCertificate_of_hasNonnegativeAxiomRepresentation hP
  have hcertP' : certP.DegreeLE (2 * (2 * ell)) :=
    hcertP.trans (cleaningFormula_width_le hell)
  have hwitnessCertificate :
      (curious.witnessingCertificate (cleaningFormula hell)).DegreeLE
        (cleaningDegree ell degree) :=
    JuntaRep.witnessingCertificate_degreeLE hcurious_degree
  have hP'certificate :
      HasNSCertificateDegreeLE (cleaningFormula hell) P'
        (cleaningCertificateDegree ell degree) := by
    refine ⟨certP.sub (curious.witnessingCertificate (cleaningFormula hell)), ?_⟩
    exact NSCertificate.sub_degree_le_max hcertP' hwitnessCertificate
  refine ⟨P', cleaned, hP'certificate, ?_, hcleaned_nonnegative, hcleaned_degree,
    hcleaned_aligned, hcleaned_curious, hcleaned_nonwitnessing, ?_⟩
  · intro z
    have hpartition := JuntaRep.eval_witnessingPart_add_eval_nonWitnessingPart
      (cleaningFormula hell) curious z
    change P z - (curious.witnessingPart (cleaningFormula hell)).eval z =
      1 + (curious.nonWitnessingPart (cleaningFormula hell)).eval z + E z
    rw [hidentity, ← hcurious_eval, ← hpartition]
    ring
  · intro z
    have hfilter := JuntaRep.eval_nonWitnessingPart_le
      (F := cleaningFormula hell) hcurious_nonnegative z
    refine ⟨hfilter.1, hfilter.2.trans_eq ?_⟩
    exact congrFun hcurious_eval z

end SoD.Preprocess

end Revres
