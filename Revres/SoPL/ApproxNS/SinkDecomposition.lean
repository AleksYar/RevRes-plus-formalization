import Revres.SoPL.Hardness

/-!
# Canonical SoPL certificate decomposition by active last-row outputs

Every clause of the deduplicated canonical search CNF has one fixed producer chosen by
`Encoding.clauseOutput`. Grouping complete certificate summands by that choice gives an exact
polynomial partition. On path-family inputs, only groups assigned to active last-row outputs can
have nonzero evaluations.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace SoPL

variable {ell : ℕ} {hell : 0 < ell}
variable {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}

/-- One complete multiplier-times-clause summand of the canonical SoPL certificate. -/
noncomputable def clauseSummand
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (C : ↑(Encoding.searchCNF ell hell)) :
    BooleanPolynomial (Encoding.variableCount ell) :=
  cert.multiplier C.1 * C.1.clausePolynomial

theorem totalDegree_clauseSummand_le
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (C : ↑(Encoding.searchCNF ell hell)) :
    (clauseSummand cert C).totalDegree ≤ cert.degree :=
  (NSCertificate.degree_le_iff.mp
    (show cert.DegreeLE cert.degree from le_rfl)) C.1 C.2

/-- A non-falsified clause contributes zero after Boolean evaluation. -/
theorem evalBoolean_clauseSummand_eq_zero_of_not_falsified
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (C : ↑(Encoding.searchCNF ell hell))
    (y : Fin (Encoding.variableCount ell) → F2)
    (hC : ¬C.1.Falsified y) :
    evalBoolean y (clauseSummand cert C) = 0 := by
  rw [clauseSummand, evalBoolean_mul,
    Clause.clausePolynomial_evalBoolean_eq_if, if_neg hC, mul_zero]

/-- The complete summands whose fixed canonical producer is `o`. -/
noncomputable def outputPolynomial
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (o : SoPL.Output (BinaryPointer.order ell)) :
    BooleanPolynomial (Encoding.variableCount ell) :=
  ∑ C : ↑(Encoding.searchCNF ell hell),
    if Encoding.clauseOutput C = o then clauseSummand cert C else 0

/-- The contribution assigned to the active-last output at `u`. -/
noncomputable def sinkPolynomial
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (u : Encoding.Node ell) :
    BooleanPolynomial (Encoding.variableCount ell) :=
  outputPolynomial cert (.activeLast u)

theorem totalDegree_outputPolynomial_le
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (o : SoPL.Output (BinaryPointer.order ell)) :
    (outputPolynomial cert o).totalDegree ≤ cert.degree := by
  unfold outputPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro C _hC
  split_ifs
  · exact totalDegree_clauseSummand_le cert C
  · simp

theorem totalDegree_sinkPolynomial_le
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (u : Encoding.Node ell) :
    (sinkPolynomial cert u).totalDegree ≤ cert.degree := by
  exact totalDegree_outputPolynomial_le cert (.activeLast u)

theorem totalDegree_sinkPolynomial_le_of_degreeLE
    {cert : NSCertificate (Encoding.searchCNF ell hell) Q}
    {degree : ℕ} (hdegree : cert.DegreeLE degree)
    (u : Encoding.Node ell) :
    (sinkPolynomial cert u).totalDegree ≤ degree :=
  (totalDegree_sinkPolynomial_le cert u).trans hdegree

/-- Partition every canonical clause exactly once by its fixed chosen producer. -/
theorem combinationPolynomial_eq_sum_outputs
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q) :
    cert.combinationPolynomial =
      ∑ o : SoPL.Output (BinaryPointer.order ell), outputPolynomial cert o := by
  classical
  calc
    cert.combinationPolynomial =
        ∑ C : ↑(Encoding.searchCNF ell hell), clauseSummand cert C := by
      rw [NSCertificate.combinationPolynomial]
      exact Finset.sum_subtype (Encoding.searchCNF ell hell)
        (fun _C ↦ Iff.rfl) (fun C ↦ cert.multiplier C * C.clausePolynomial)
    _ = ∑ C : ↑(Encoding.searchCNF ell hell),
          ∑ o : SoPL.Output (BinaryPointer.order ell),
            if Encoding.clauseOutput C = o then clauseSummand cert C else 0 := by
      apply Finset.sum_congr rfl
      intro C _hC
      simp
    _ = ∑ o : SoPL.Output (BinaryPointer.order ell), outputPolynomial cert o := by
      rw [Finset.sum_comm]
      rfl

/-- A producer group cannot contribute at an assignment where that output is invalid. -/
theorem evalBoolean_outputPolynomial_eq_zero_of_not_valid
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (o : SoPL.Output (BinaryPointer.order ell))
    (y : Fin (Encoding.variableCount ell) → F2)
    (hvalid : ¬SoPL.Valid (BinaryPointer.order_pos hell)
      (Encoding.decodeInput ell y) o) :
    evalBoolean y (outputPolynomial cert o) = 0 := by
  rw [outputPolynomial, evalBoolean_finset_sum]
  apply Finset.sum_eq_zero
  intro C _hC
  by_cases houtput : Encoding.clauseOutput C = o
  · rw [if_pos houtput]
    by_cases hCfalsified : C.1.Falsified y
    · exact (hvalid (houtput ▸ Encoding.clauseOutput_valid C hCfalsified)).elim
    · exact evalBoolean_clauseSummand_eq_zero_of_not_falsified cert C y hCfalsified
  · rw [if_neg houtput, evalBoolean_zero]

private def outputSumEquiv (n : ℕ) :
    SoPL.Output n ≃ Unit ⊕ (GridNode n ⊕ GridNode n) where
  toFun
    | .inactiveSource => .inl ()
    | .activeLast u => .inr (.inl u)
    | .properSink v => .inr (.inr v)
  invFun
    | .inl _ => .inactiveSource
    | .inr (.inl u) => .activeLast u
    | .inr (.inr v) => .properSink v
  left_inv o := by cases o <;> rfl
  right_inv s := by rcases s with (_ | _ | _) <;> rfl

private theorem sum_output_decomposition
    {n : ℕ} {M : Type*} [AddCommMonoid M]
    (f : SoPL.Output n → M) :
    ∑ o, f o =
      f .inactiveSource + ∑ u, f (.activeLast u) + ∑ v, f (.properSink v) := by
  let g : Unit ⊕ (GridNode n ⊕ GridNode n) → M
    | .inl _ => f .inactiveSource
    | .inr (.inl u) => f (.activeLast u)
    | .inr (.inr v) => f (.properSink v)
  calc
    ∑ o, f o = ∑ s, g s :=
      Fintype.sum_equiv (outputSumEquiv n) f g (by
        intro o
        cases o <;> rfl)
    _ = f .inactiveSource + ∑ u, f (.activeLast u) +
          ∑ v, f (.properSink v) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [g, add_assoc]

/-- On a path-family input, all non-active-last producer groups vanish. -/
theorem eval_combination_eq_sum_activeLast
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    {y : Fin (Encoding.variableCount ell) → F2}
    (hpath : IsEncodedPathFamily ell hell y) :
    evalBoolean y cert.combinationPolynomial =
      ∑ u : Encoding.Node ell, evalBoolean y (sinkPolynomial cert u) := by
  change Nonempty (PathFamilyWitness (BinaryPointer.order_pos hell)
    (Encoding.decodeInput ell y)) at hpath
  rcases hpath with ⟨W⟩
  have hinactive :
      ¬SoPL.Valid (BinaryPointer.order_pos hell) (Encoding.decodeInput ell y)
        .inactiveSource := by
    intro hvalid
    obtain ⟨u, hu, _hlast, _hactive⟩ := pathFamily_solutions_last_row W hvalid
    cases hu
  have hproper : ∀ v : Encoding.Node ell,
      ¬SoPL.Valid (BinaryPointer.order_pos hell) (Encoding.decodeInput ell y)
        (.properSink v) := by
    intro v hvalid
    obtain ⟨u, hu, _hlast, _hactive⟩ := pathFamily_solutions_last_row W hvalid
    cases hu
  rw [combinationPolynomial_eq_sum_outputs, evalBoolean_finset_sum,
    sum_output_decomposition]
  simp only [sinkPolynomial]
  rw [evalBoolean_outputPolynomial_eq_zero_of_not_valid cert
    .inactiveSource y hinactive]
  simp [evalBoolean_outputPolynomial_eq_zero_of_not_valid cert, hproper]

namespace Encoding

/-- The exact semantic set of active last-row nodes in an encoded input. -/
noncomputable def activeLastSet {ell : ℕ}
    (y : Fin (variableCount ell) → F2) : Finset (Node ell) := by
  classical
  exact Finset.univ.filter fun u ↦
    u.IsLastRow ∧ (decodeInput ell y).Active u

@[simp]
theorem mem_activeLastSet {ell : ℕ}
    {y : Fin (variableCount ell) → F2} {u : Node ell} :
    u ∈ activeLastSet y ↔
      u.IsLastRow ∧ (decodeInput ell y).Active u := by
  classical
  simp [activeLastSet]

end Encoding

/-- Restrict the path-family decomposition to exactly the active last-row nodes. -/
theorem eval_combination_eq_sum_active_sinks
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    {y : Fin (Encoding.variableCount ell) → F2}
    (hpath : IsEncodedPathFamily ell hell y) :
    evalBoolean y cert.combinationPolynomial =
      ∑ u ∈ Encoding.activeLastSet y,
        evalBoolean y (sinkPolynomial cert u) := by
  rw [eval_combination_eq_sum_activeLast cert hpath]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _hu hnotActive
  exact evalBoolean_outputPolynomial_eq_zero_of_not_valid cert
    (.activeLast u) y (by
      simpa only [SoPL.Valid, Encoding.mem_activeLastSet] using hnotActive)

/-- The represented certificate value is the sum of its active sink contributions. -/
theorem represented_eq_sum_active_sinks
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    {y : Fin (Encoding.variableCount ell) → F2}
    (hpath : IsEncodedPathFamily ell hell y) :
    Q y =
      ∑ u ∈ Encoding.activeLastSet y,
        evalBoolean y (sinkPolynomial cert u) := by
  calc
    Q y = evalBoolean y cert.combinationPolynomial :=
      (NSCertificate.evalBoolean_combinationPolynomial cert y).symm
    _ = ∑ u ∈ Encoding.activeLastSet y,
          evalBoolean y (sinkPolynomial cert u) :=
      eval_combination_eq_sum_active_sinks cert hpath

end SoPL

end Revres
