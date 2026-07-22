import Revres.SoD.Amplification.Structural

/-!
# One-step amplification

Assemble hard-input growth, cleanup selection, and the structural update into
one transition between good amplification states.
-/

namespace Revres

open Lemma53

namespace SoD

namespace Amplification

variable {ell proofDegree degreeLowerBound juntaDegree : ℕ}

/-- The concrete witnesses selected by one amplification stage. -/
theorem exists_amplification_step_data
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {P E : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z)
    (herror : ErrorControlled E)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree : 2 * proofDegree * (7 * ell) < degreeLowerBound)
    (hNonnegative : JR.Nonnegative)
    (hJuntaDegree : JR.DegreeLE juntaDegree)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    (hsmall : 100 * juntaDegree ≤ ActiveEdge.localOrder ell) :
    ∃ y, SoPL.IsEncodedPathFamily ell hell y ∧
      ∃ R,
        ∃ hR : R ∈ SoD.nextMacroRowCandidates
            (BinaryPointer.order_pos hell) s.currentBox,
          GoodState hell JR (nextState hgood hinternal y R hR) := by
  obtain ⟨y, hy, _hPgrowth, hJgrowth⟩ := exists_path_input_growth
    hgood hinternal hcert hidentity herror hHard htransferDegree
  obtain ⟨R, hR, hcleanup⟩ := exists_candidate_cleanup_growth
    hgood hinternal y hNonnegative hJuntaDegree hAlign hCurious hNonWitness
      hsmall hJgrowth
  dsimp only at hcleanup
  refine ⟨y, hy, R, hR, ?_⟩
  apply good_nextState hgood hinternal y hy R hR
  intro z hagree
  exact le_of_lt (hcleanup.2 z hagree)

/--
Paper correspondence: Lemma `lem:one-step-amplification` in
`revres_xor_superpoly_lower_bound_restriction_notation.tex`.

Mathematical content: One nonterminal good state advances by one macro-row and
grows its certified lower bound.

Formalization note: The paper records a factor `4 / 3`; under its concrete
hypotheses the Lean capstone proves the stronger explicit factor `7 / 5`.

Used by: `amplification_iterate_from` and the iterated amplification capstone.
-/
theorem amplification_step
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {P E : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z)
    (herror : ErrorControlled E)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree : 2 * proofDegree * (7 * ell) < degreeLowerBound)
    (hNonnegative : JR.Nonnegative)
    (hJuntaDegree : JR.DegreeLE juntaDegree)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    (hsmall : 100 * juntaDegree ≤ ActiveEdge.localOrder ell) :
    ∃ next, GoodState hell JR next ∧
      next.stage = s.stage + 1 ∧ (7 / 5 : ℝ) * s.B ≤ next.B := by
  obtain ⟨y, _hy, R, hR, hnext⟩ := exists_amplification_step_data
    hgood hinternal hcert hidentity herror hHard htransferDegree
      hNonnegative hJuntaDegree hAlign hCurious hNonWitness hsmall
  refine ⟨nextState hgood hinternal y R hR, hnext, ?_, ?_⟩
  · exact nextState_stage hgood hinternal y R hR
  · rw [nextState_B]

end Amplification

end SoD

end Revres
