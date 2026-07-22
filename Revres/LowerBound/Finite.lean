import Revres.LowerBound.Abstract
import Revres.SoD.Amplification.Iterate

/-!
# Conditional finite RevRes lower bound for Sink-of-DAG

The completed preprocessing and amplification argument supplies the concrete
robust amplification property required by the abstract lower-bound theorem.
The external SoPL path-family hardness statement remains an explicit
hypothesis.
-/

namespace Revres

/-- The cleaned Sink-of-DAG formula has the robust amplification property,
conditional on the explicit SoPL hardness and degree hypotheses. -/
theorem sod_cleaningFormula_robustAmplification
    {ell degree degreeLowerBound : ℕ}
    (hell : 0 < ell)
    (hlocal : 1 < SoD.ActiveEdge.localOrder ell)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree :
      2 * SoD.Preprocess.cleaningCertificateDegree ell degree * (7 * ell) <
        degreeLowerBound)
    (hsmall :
      100 * SoD.Preprocess.cleaningDegree ell degree ≤
        SoD.ActiveEdge.localOrder ell) :
    RobustAmplificationProperty
      (SoD.Preprocess.cleaningFormula hell)
      degree
      SoD.Amplification.errorThreshold
      ((7 / 5 : ℝ) ^ (SoD.ActiveEdge.localOrder ell - 1) - 1) := by
  intro P E JR hP hnonnegative hdegree hidentity herror
  obtain ⟨P', JR', hcert, hidentity', hnonnegative', hdegree', halign,
      hcurious, hnonWitness, hdomination⟩ :=
    SoD.Preprocess.preprocess hell hP hnonnegative hdegree hidentity
  obtain ⟨state, hgood, _hstage, hbound⟩ :=
    SoD.Amplification.exists_last_amplification_state
      hlocal hcert hidentity' herror hHard htransferDegree hnonnegative'
        hdegree' halign hcurious hnonWitness hsmall
  refine ⟨state.nullAssignment, ?_⟩
  have hmatches :
      state.restriction.Matches state.nullAssignment := by
    simpa [SoD.Amplification.AmpState.nullAssignment] using
      SoD.Amplification.Restriction.matches_nullAssignment state.restriction
  have hnumerical :
      state.B ≤ 1 + JR'.eval state.nullAssignment :=
    hgood.numerical state.nullAssignment hmatches
  calc
    (7 / 5 : ℝ) ^ (SoD.ActiveEdge.localOrder ell - 1) - 1 ≤
        JR'.eval state.nullAssignment := by
      linarith
    _ ≤ JR.eval state.nullAssignment := (hdomination state.nullAssignment).2

/-- The concrete small-error/large-error dichotomy for the lifted cleaned
Sink-of-DAG formula. -/
theorem finite_revres_lower_bound_dichotomy
    {ell degree degreeLowerBound : ℕ}
    (hell : 0 < ell)
    (hlocal : 1 < SoD.ActiveEdge.localOrder ell)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree :
      2 * SoD.Preprocess.cleaningCertificateDegree ell degree * (7 * ell) <
        degreeLowerBound)
    (hsmall :
      100 * SoD.Preprocess.cleaningDegree ell degree ≤
        SoD.ActiveEdge.localOrder ell)
    (π : RevResRefutation
      (indexLift (SoD.Preprocess.cleaningFormula hell))) :
    ((7 / 5 : ℝ) ^ (SoD.ActiveEdge.localOrder ell - 1) - 1 ≤
        (2 : ℝ) * π.length) ∨
      SoD.Amplification.errorThreshold <
        (2 : ℝ) * π.length * decompositionError degree := by
  exact revres_lower_bound_dichotomy π
    (sod_cleaningFormula_robustAmplification hell hlocal hHard
      htransferDegree hsmall)

/-- Exact finite conditional lower bound for every RevRes refutation of the
lifted cleaned Sink-of-DAG formula. -/
theorem finite_revres_lower_bound
    {ell degree degreeLowerBound : ℕ}
    (hell : 0 < ell)
    (hlocal : 1 < SoD.ActiveEdge.localOrder ell)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree :
      2 * SoD.Preprocess.cleaningCertificateDegree ell degree * (7 * ell) <
        degreeLowerBound)
    (hsmall :
      100 * SoD.Preprocess.cleaningDegree ell degree ≤
        SoD.ActiveEdge.localOrder ell)
    (π : RevResRefutation
      (indexLift (SoD.Preprocess.cleaningFormula hell))) :
    (1 / 2 : ℝ) *
        min
          ((7 / 5 : ℝ) ^ (SoD.ActiveEdge.localOrder ell - 1) - 1)
          (SoD.Amplification.errorThreshold / decompositionError degree) ≤
      (π.length : ℝ) := by
  exact revres_lower_bound_of_amplification π
    (sod_cleaningFormula_robustAmplification hell hlocal hHard
      htransferDegree hsmall)

end Revres
