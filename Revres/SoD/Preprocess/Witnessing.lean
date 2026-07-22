import Revres.Conical.Representation
import Revres.Polynomial.Certificate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Witnessing terms in explicit conical juntas

A term witnesses a clause when it contains the clause's complete falsifying assignment. Such a
term factors through the clause polynomial. Filtering a junta on this predicate separates the
part that can be moved into a Nullstellensatz certificate from the nonwitnessing remainder.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace Term

variable {N : ℕ}

/-- The term contains every literal of the clause's falsifying partial assignment. -/
def Witnesses (t : Term N) (C : Clause N) : Prop :=
  ∀ i b, C i = some b → t.val i = some b

/-- The term witnesses at least one clause of `F`. -/
def WitnessesFormula (F : CNF N) (t : Term N) : Prop :=
  ∃ C ∈ F, t.Witnesses C

noncomputable local instance witnessesFormulaDecidable (F : CNF N) (t : Term N) :
    Decidable (t.WitnessesFormula F) :=
  Classical.propDecidable _

theorem witnessesFormula_iff {F : CNF N} {t : Term N} :
    t.WitnessesFormula F ↔ ∃ C ∈ F, t.Witnesses C :=
  Iff.rfl

namespace Witnesses

theorem support_subset {t : Term N} {C : Clause N} (h : t.Witnesses C) :
    C.support ⊆ t.support := by
  intro i hi
  obtain ⟨b, hCb⟩ := Clause.exists_eq_some_of_mem_support hi
  exact Term.mem_support.mpr (by simp [h i b hCb])

theorem falsified_of_matches {t : Term N} {C : Clause N} (h : t.Witnesses C)
    {z : Fin N → Lemma53.F2} (hmatch : t.Matches z) : C.Falsified z := by
  intro i b hCb
  exact hmatch i b (h i b hCb)

theorem indicator_mul_clauseIndicator {t : Term N} {C : Clause N}
    (h : t.Witnesses C) (z : Fin N → Lemma53.F2) :
    t.indicator z = t.indicator z * C.realFalsifiedIndicator z := by
  by_cases hmatch : t.Matches z
  · have hfalsified := h.falsified_of_matches hmatch
    simp [Term.indicator, Clause.realFalsifiedIndicator, hmatch, hfalsified]
  · simp [Term.indicator, Clause.realFalsifiedIndicator, hmatch]

end Witnesses

/-- Remove exactly the coordinates occurring in `C` from `t`. -/
def withoutClause (t : Term N) (C : Clause N) : Term N where
  val i := if C i = none then t.val i else none

theorem support_withoutClause (t : Term N) (C : Clause N) :
    (t.withoutClause C).support = t.support \ C.support := by
  ext i
  by_cases hC : C i = none <;> simp [withoutClause, hC]

theorem withoutClause_support_disjoint (t : Term N) (C : Clause N) :
    Disjoint (t.withoutClause C).support C.support := by
  rw [support_withoutClause]
  exact Finset.sdiff_disjoint

theorem Witnesses.support_eq_withoutClause_union {t : Term N} {C : Clause N}
    (h : t.Witnesses C) :
    t.support = (t.withoutClause C).support ∪ C.support := by
  rw [support_withoutClause]
  exact (Finset.sdiff_union_of_subset h.support_subset).symm

/-- The ordinary real polynomial represented by a canonical term. -/
noncomputable def toPolynomial (t : Term N) : BooleanPolynomial N :=
  Clause.clausePolynomial t.val

@[simp]
theorem clauseSupport_val (t : Term N) : Clause.support t.val = t.support :=
  rfl

theorem evalBoolean_toPolynomial (t : Term N) (z : Fin N → Lemma53.F2) :
    evalBoolean z t.toPolynomial = t.indicator z := by
  rw [toPolynomial, Clause.clausePolynomial_evalBoolean_eq_if]
  by_cases hmatch : t.Matches z <;>
    simp [Term.indicator, Term.Matches, Clause.Falsified] at *

theorem totalDegree_toPolynomial (t : Term N) :
    t.toPolynomial.totalDegree = t.degree := by
  rw [toPolynomial, Clause.totalDegree_clausePolynomial_eq]
  rfl

theorem Witnesses.witnessing_factor {t : Term N} {C : Clause N}
    (h : t.Witnesses C) :
    t.toPolynomial = (t.withoutClause C).toPolynomial * C.clausePolynomial := by
  classical
  unfold toPolynomial Clause.clausePolynomial
  rw [clauseSupport_val, clauseSupport_val]
  rw [h.support_eq_withoutClause_union,
    Finset.prod_union (withoutClause_support_disjoint t C)]
  apply congrArg₂ (fun p q : BooleanPolynomial N ↦ p * q)
  · apply Finset.prod_congr rfl
    intro i hi
    have hiC : i ∉ C.support := by
      intro hiC
      exact (Finset.disjoint_left.mp (withoutClause_support_disjoint t C)) hi hiC
    have hCi : C i = none := Clause.not_mem_support.mp hiC
    simp [withoutClause, hCi]
  · apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨b, hCb⟩ := Clause.exists_eq_some_of_mem_support hi
    rw [h i b hCb, hCb]

theorem Witnesses.witnessing_factor_eval {t : Term N} {C : Clause N}
    (h : t.Witnesses C) (z : Fin N → Lemma53.F2) :
    t.indicator z =
      evalBoolean z ((t.withoutClause C).toPolynomial * C.clausePolynomial) := by
  rw [← h.witnessing_factor, evalBoolean_toPolynomial]

theorem Witnesses.totalDegree_factor {t : Term N} {C : Clause N}
    (h : t.Witnesses C) :
    ((t.withoutClause C).toPolynomial * C.clausePolynomial).totalDegree = t.degree := by
  rw [← h.witnessing_factor, totalDegree_toPolynomial]

/-- A stable choice of one witnessed clause. Its fallback value is used only for nonwitnessing
terms. -/
noncomputable def witnessClause (F : CNF N) (t : Term N) : Clause N := by
  classical
  exact if h : t.WitnessesFormula F then Classical.choose h else Clause.empty N

private theorem witnessClause_spec {F : CNF N} {t : Term N}
    (h : t.WitnessesFormula F) :
    t.witnessClause F ∈ F ∧ t.Witnesses (t.witnessClause F) := by
  rw [witnessClause, dif_pos h]
  exact Classical.choose_spec h

theorem witnessClause_mem {F : CNF N} {t : Term N}
    (h : t.WitnessesFormula F) : t.witnessClause F ∈ F :=
  (witnessClause_spec h).1

theorem witnesses_witnessClause {F : CNF N} {t : Term N}
    (h : t.WitnessesFormula F) : t.Witnesses (t.witnessClause F) :=
  (witnessClause_spec h).2

/-- The one-clause certificate for a scalar multiple of a witnessing term. -/
noncomputable def singleWitnessCertificate
    (F : CNF N) (t : Term N) (C : Clause N)
    (hC : C ∈ F) (hwitness : t.Witnesses C) (coeff : ℝ) :
    NSCertificate F (fun z ↦ coeff * t.indicator z) where
  multiplier D :=
    if D = C then MvPolynomial.C coeff * (t.withoutClause C).toPolynomial else 0
  represents := by
    intro z
    unfold polynomialAxiomCombination
    rw [Finset.sum_eq_single C]
    · simp only [if_pos, evalBoolean_mul, evalBoolean_C]
      rw [mul_assoc, ← evalBoolean_mul, ← hwitness.witnessing_factor_eval z]
    · intro D hDF hDC
      simp [hDC]
    · exact fun hnot ↦ (hnot hC).elim

theorem singleWitnessCertificate_represents
    (F : CNF N) (t : Term N) (C : Clause N)
    (hC : C ∈ F) (hwitness : t.Witnesses C) (coeff : ℝ)
    (z : Fin N → Lemma53.F2) :
    coeff * t.indicator z =
      polynomialAxiomCombination F
        (t.singleWitnessCertificate F C hC hwitness coeff).multiplier z :=
  (t.singleWitnessCertificate F C hC hwitness coeff).represents z

theorem singleWitnessCertificate_degreeLE
    (F : CNF N) (t : Term N) (C : Clause N)
    (hC : C ∈ F) (hwitness : t.Witnesses C) (coeff : ℝ) :
    (t.singleWitnessCertificate F C hC hwitness coeff).DegreeLE t.degree := by
  rw [NSCertificate.degree_le_iff]
  intro D hDF
  by_cases hDC : D = C
  · subst D
    change (((if C = C then
      MvPolynomial.C coeff * (t.withoutClause C).toPolynomial else 0) *
        C.clausePolynomial).totalDegree ≤ t.degree)
    rw [if_pos rfl]
    calc
      ((MvPolynomial.C coeff * (t.withoutClause C).toPolynomial) *
          C.clausePolynomial).totalDegree =
          (MvPolynomial.C coeff *
            ((t.withoutClause C).toPolynomial * C.clausePolynomial)).totalDegree := by
            rw [mul_assoc]
      _ ≤ (MvPolynomial.C coeff : BooleanPolynomial N).totalDegree +
          ((t.withoutClause C).toPolynomial * C.clausePolynomial).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = t.degree := by
        rw [MvPolynomial.totalDegree_C, hwitness.totalDegree_factor]
        simp
  · change (((if D = C then
      MvPolynomial.C coeff * (t.withoutClause C).toPolynomial else 0) *
        D.clausePolynomial).totalDegree ≤ t.degree)
    rw [if_neg hDC]
    simp

end Term

namespace JuntaRep

variable {N degree : ℕ}

/-- Retain exactly the terms that witness at least one clause of `F`. -/
noncomputable def witnessingPart (F : CNF N) (JR : JuntaRep N) : JuntaRep N := by
  classical
  exact JR.filter (Term.WitnessesFormula F)

/-- Retain exactly the terms that witness no clause of `F`. -/
noncomputable def nonWitnessingPart (F : CNF N) (JR : JuntaRep N) : JuntaRep N := by
  classical
  exact JR.filter (fun t ↦ ¬t.WitnessesFormula F)

/-- Every nonzero term witnesses no clause of the formula. -/
def NonWitnessing (F : CNF N) (JR : JuntaRep N) : Prop :=
  ∀ t ∈ JR.support, ¬t.WitnessesFormula F

theorem mem_support_witnessingPart {F : CNF N} {JR : JuntaRep N} {t : Term N} :
    t ∈ (JR.witnessingPart F).support ↔
      t ∈ JR.support ∧ t.WitnessesFormula F := by
  classical
  simp [witnessingPart]

theorem mem_support_nonWitnessingPart {F : CNF N} {JR : JuntaRep N} {t : Term N} :
    t ∈ (JR.nonWitnessingPart F).support ↔
      t ∈ JR.support ∧ ¬t.WitnessesFormula F := by
  classical
  simp [nonWitnessingPart]

theorem witnessingPart_add_nonWitnessingPart (F : CNF N) (JR : JuntaRep N) :
    JR.witnessingPart F + JR.nonWitnessingPart F = JR := by
  classical
  exact Finsupp.filter_add_filter_not JR (Term.WitnessesFormula F)

theorem eval_witnessingPart_add_eval_nonWitnessingPart
    (F : CNF N) (JR : JuntaRep N) (z : Fin N → Lemma53.F2) :
    (JR.witnessingPart F).eval z + (JR.nonWitnessingPart F).eval z = JR.eval z := by
  rw [← JuntaRep.eval_add, witnessingPart_add_nonWitnessingPart]

theorem witnessingPart_nonnegative {F : CNF N} {JR : JuntaRep N}
    (hJR : JR.Nonnegative) : (JR.witnessingPart F).Nonnegative := by
  classical
  intro t
  rw [witnessingPart, Finsupp.filter_apply]
  split <;> simp_all [hJR t]

theorem nonWitnessingPart_nonnegative {F : CNF N} {JR : JuntaRep N}
    (hJR : JR.Nonnegative) : (JR.nonWitnessingPart F).Nonnegative := by
  classical
  intro t
  rw [nonWitnessingPart, Finsupp.filter_apply]
  split <;> simp_all [hJR t]

theorem witnessingPart_degreeLE {F : CNF N} {JR : JuntaRep N}
    (hdegree : JR.DegreeLE degree) : (JR.witnessingPart F).DegreeLE degree := by
  classical
  intro t ht
  exact hdegree t (mem_support_witnessingPart.mp ht).1

theorem nonWitnessingPart_degreeLE {F : CNF N} {JR : JuntaRep N}
    (hdegree : JR.DegreeLE degree) : (JR.nonWitnessingPart F).DegreeLE degree := by
  classical
  intro t ht
  exact hdegree t (mem_support_nonWitnessingPart.mp ht).1

theorem nonWitnessingPart_nonWitnessing (F : CNF N) (JR : JuntaRep N) :
    (JR.nonWitnessingPart F).NonWitnessing F := by
  classical
  intro t ht
  exact (mem_support_nonWitnessingPart.mp ht).2

theorem eval_nonWitnessingPart_le {F : CNF N} {JR : JuntaRep N}
    (hJR : JR.Nonnegative) (z : Fin N → Lemma53.F2) :
    0 ≤ (JR.nonWitnessingPart F).eval z ∧
      (JR.nonWitnessingPart F).eval z ≤ JR.eval z := by
  refine ⟨JuntaRep.eval_nonneg (nonWitnessingPart_nonnegative hJR) z, ?_⟩
  have hwitnessing : 0 ≤ (JR.witnessingPart F).eval z :=
    JuntaRep.eval_nonneg (witnessingPart_nonnegative hJR) z
  have hpartition := eval_witnessingPart_add_eval_nonWitnessingPart F JR z
  rw [← hpartition]
  exact le_add_of_nonneg_left hwitnessing

private noncomputable def supportedWitnessFunction (F : CNF N) (JR : JuntaRep N)
    (t : ↑(JR.witnessingPart F).support) :
    (Fin N → Lemma53.F2) → ℝ :=
  fun z ↦ (JR.witnessingPart F) t.1 * t.1.indicator z

private theorem supportedWitness_witnessesFormula (F : CNF N) (JR : JuntaRep N)
    (t : ↑(JR.witnessingPart F).support) : t.1.WitnessesFormula F :=
  (mem_support_witnessingPart.mp t.2).2

private noncomputable def supportedWitnessCertificate (F : CNF N) (JR : JuntaRep N)
    (t : ↑(JR.witnessingPart F).support) :
    NSCertificate F (supportedWitnessFunction F JR t) :=
  t.1.singleWitnessCertificate F (t.1.witnessClause F)
    (Term.witnessClause_mem (supportedWitness_witnessesFormula F JR t))
    (Term.witnesses_witnessClause (supportedWitness_witnessesFormula F JR t))
    ((JR.witnessingPart F) t.1)

/-- The sum of the one-clause certificates for all witnessing terms. -/
noncomputable def witnessingCertificate (F : CNF N) (JR : JuntaRep N) :
    NSCertificate F (JR.witnessingPart F).eval := by
  let certSum := NSCertificate.finsetSum Finset.univ
    (supportedWitnessFunction F JR) (supportedWitnessCertificate F JR)
  apply certSum.congr
  funext z
  change (∑ t : ↑(JR.witnessingPart F).support,
    (JR.witnessingPart F) t.1 * t.1.indicator z) = (JR.witnessingPart F).eval z
  rw [JuntaRep.eval, Finsupp.sum]
  exact Finset.sum_coe_sort (JR.witnessingPart F).support
    (fun t ↦ (JR.witnessingPart F) t * t.indicator z)

theorem witnessingCertificate_represents (F : CNF N) (JR : JuntaRep N)
    (z : Fin N → Lemma53.F2) :
    (JR.witnessingPart F).eval z =
      polynomialAxiomCombination F (JR.witnessingCertificate F).multiplier z :=
  (JR.witnessingCertificate F).represents z

theorem witnessingCertificate_degreeLE {F : CNF N} {JR : JuntaRep N}
    (hdegree : JR.DegreeLE degree) :
    (JR.witnessingCertificate F).DegreeLE degree := by
  unfold witnessingCertificate
  apply NSCertificate.congr_degreeLE
  apply NSCertificate.finsetSum_degree_le
  intro t _ht
  exact (Term.singleWitnessCertificate_degreeLE F t.1 (t.1.witnessClause F)
    (Term.witnessClause_mem (supportedWitness_witnessesFormula F JR t))
    (Term.witnesses_witnessClause (supportedWitness_witnessesFormula F JR t))
    ((JR.witnessingPart F) t.1)).trans
      (hdegree t.1 (mem_support_witnessingPart.mp t.2).1)

/-- Remove every witnessing term from a robust identity and subtract its certificate from `P`. -/
theorem eliminateWitnessing
    {F : CNF N}
    {P E : (Fin N → Lemma53.F2) → ℝ}
    {JR : JuntaRep N}
    {proofDegree juntaDegree : ℕ}
    (hcert : HasNSCertificateDegreeLE F P proofDegree)
    (hnonnegative : JR.Nonnegative)
    (hdegree : JR.DegreeLE juntaDegree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z) :
    ∃ (P' : (Fin N → Lemma53.F2) → ℝ) (JR' : JuntaRep N),
      HasNSCertificateDegreeLE F P' (max proofDegree juntaDegree) ∧
      (∀ z, P' z = 1 + JR'.eval z + E z) ∧
      JR'.Nonnegative ∧
      JR'.DegreeLE juntaDegree ∧
      JR'.NonWitnessing F ∧
      (∀ z, 0 ≤ JR'.eval z ∧ JR'.eval z ≤ JR.eval z) := by
  obtain ⟨certP, hcertP⟩ := hcert
  let W : JuntaRep N := JR.witnessingPart F
  let JR' : JuntaRep N := JR.nonWitnessingPart F
  let P' : (Fin N → Lemma53.F2) → ℝ := P - W.eval
  have hWdegree : (JR.witnessingCertificate F).DegreeLE juntaDegree :=
    witnessingCertificate_degreeLE hdegree
  have hcert' : HasNSCertificateDegreeLE F P' (max proofDegree juntaDegree) := by
    refine ⟨certP.sub (JR.witnessingCertificate F), ?_⟩
    exact NSCertificate.sub_degree_le_max hcertP hWdegree
  refine ⟨P', JR', hcert', ?_,
    nonWitnessingPart_nonnegative hnonnegative,
    nonWitnessingPart_degreeLE hdegree,
    nonWitnessingPart_nonWitnessing F JR, ?_⟩
  · intro z
    have hpartition := eval_witnessingPart_add_eval_nonWitnessingPart F JR z
    change P z - (JR.witnessingPart F).eval z =
      1 + (JR.nonWitnessingPart F).eval z + E z
    rw [hidentity, ← hpartition]
    ring
  · intro z
    exact eval_nonWitnessingPart_le hnonnegative z

end JuntaRep

end Revres
