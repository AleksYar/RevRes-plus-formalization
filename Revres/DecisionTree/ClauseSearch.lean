import Revres.DecisionTree.Read
import Revres.DecisionTree.SearchCNF

/-!
# Clause-search decision trees

This module supplies two generic trees used by decision-tree formulations: checking a target
clause through mapped input trees, and returning the canonical clause of the accepting verifier
leaf reached by an assignment.
-/

namespace Revres

open Lemma53

namespace DecisionTree

variable {M N : ℕ}

private noncomputable def checkMappedList
    (inputTree : Fin N → DecisionTree M F2) (C : Clause N) :
    List (Fin N) → DecisionTree M Bool
  | [] => .leaf true
  | i :: indices =>
      (inputTree i).bind fun value =>
        match C i with
        | none => checkMappedList inputTree C indices
        | some expected =>
            if value = expected then checkMappedList inputTree C indices else .leaf false

private theorem eval_checkMappedList
    (inputTree : Fin N → DecisionTree M F2) (C : Clause N)
    (indices : List (Fin N)) (y : Fin M → F2) :
    (checkMappedList inputTree C indices).eval y = true ↔
      ∀ i ∈ indices, ∀ b, C i = some b → (inputTree i).eval y = b := by
  induction indices with
  | nil => simp [checkMappedList]
  | cons i indices ih =>
      cases hi : C i with
      | none => simp [checkMappedList, hi, ih]
      | some expected =>
          by_cases hvalue : (inputTree i).eval y = expected
          · simpa [checkMappedList, hi, hvalue] using ih
          · simp [checkMappedList, hi, hvalue]

private theorem depth_checkMappedList_le
    (inputTree : Fin N → DecisionTree M F2) (C : Clause N)
    (hdepth : ∀ i, (inputTree i).depth ≤ d) (indices : List (Fin N)) :
    (checkMappedList inputTree C indices).depth ≤ indices.length * d := by
  induction indices with
  | nil => simp [checkMappedList]
  | cons i indices ih =>
      let next := fun value : F2 =>
        match C i with
        | none => checkMappedList inputTree C indices
        | some expected =>
            if value = expected then checkMappedList inputTree C indices else .leaf false
      have hnext : ∀ value, (next value).depth ≤ indices.length * d := by
        intro value
        simp only [next]
        split
        · exact ih
        · split <;> simp_all
      have hbind := DecisionTree.depth_bind_le (inputTree i) next hnext
      calc
        (checkMappedList inputTree C (i :: indices)).depth ≤
            (inputTree i).depth + indices.length * d := by
          simpa [checkMappedList, next] using hbind
        _ ≤ d + indices.length * d := Nat.add_le_add_right (hdepth i) _
        _ = (i :: indices).length * d := by
          rw [List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Check a clause after computing each supported target coordinate by a source decision tree. -/
noncomputable def checkMappedClause
    (inputTree : Fin N → DecisionTree M F2) (C : Clause N) : DecisionTree M Bool :=
  checkMappedList inputTree C C.support.toList

@[simp]
theorem eval_checkMappedClause
    (inputTree : Fin N → DecisionTree M F2) (C : Clause N) (y : Fin M → F2) :
    (checkMappedClause inputTree C).eval y = true ↔
      C.Falsified (fun i => (inputTree i).eval y) := by
  rw [checkMappedClause, eval_checkMappedList]
  constructor
  · intro h i b hi
    exact h i (by simp [Clause.mem_support, hi]) b hi
  · intro h i _hi b hib
    exact h i b hib

theorem depth_checkMappedClause_le
    (inputTree : Fin N → DecisionTree M F2) (C : Clause N)
    (hdepth : ∀ i, (inputTree i).depth ≤ d) :
    (checkMappedClause inputTree C).depth ≤ C.width * d := by
  simpa [checkMappedClause, Clause.width] using
    depth_checkMappedList_le inputTree C hdepth C.support.toList

/-- Mirror a tree while labelling each leaf by its occurrence-sensitive path in the original. -/
def leafPathTree : (T : DecisionTree M α) → DecisionTree M T.LeafPath
  | .leaf a => .leaf (.leaf a)
  | .query i zeroTree oneTree =>
      .query i
        ((leafPathTree zeroTree).map fun path =>
          LeafPath.zero (i := i) (oneTree := oneTree) path)
        ((leafPathTree oneTree).map fun path =>
          LeafPath.one (i := i) (zeroTree := zeroTree) path)

@[simp]
theorem eval_leafPathTree (T : DecisionTree M α) (y : Fin M → F2) :
    T.leafPathTree.eval y = T.reachedLeaf y := by
  induction T with
  | leaf => rfl
  | query i zeroTree oneTree ihzero ihone =>
      rcases F2_eq_zero_or_one (y i) with hi | hi
      · simp [leafPathTree, reachedLeaf, hi, ihzero]
      · simp [leafPathTree, reachedLeaf, hi, ihone]

@[simp]
theorem depth_leafPathTree (T : DecisionTree M α) :
    T.leafPathTree.depth = T.depth := by
  induction T with
  | leaf => rfl
  | query i zeroTree oneTree ihzero ihone =>
      simp [leafPathTree, ihzero, ihone]

end DecisionTree

namespace SearchProblem

variable {M : ℕ}

/-- Return the canonical falsifying clause of the reached accepting verifier leaf. -/
noncomputable def acceptingClauseTree (P : SearchProblem M) (o : P.Output) :
    DecisionTree M (Option (Clause M)) :=
  (P.verifier o).leafPathTree.map fun leaf =>
    if leaf.value = true then leaf.clause else none

theorem acceptingClauseTree_depth_le (P : SearchProblem M) (o : P.Output) :
    (P.acceptingClauseTree o).depth ≤ (P.verifier o).depth := by
  simp [acceptingClauseTree]

theorem acceptingClauseTree_sound
    (P : SearchProblem M) (o : P.Output) (y : Fin M → F2) {D : Clause M}
    (h : (P.acceptingClauseTree o).eval y = some D) :
    D ∈ P.outputClauses o ∧ D.Falsified y := by
  let leaf := (P.verifier o).reachedLeaf y
  have hleaf : leaf.value = true ∧ leaf.clause = some D := by
    simpa [acceptingClauseTree, leaf] using h
  constructor
  · exact (P.mem_outputClauses_iff).mpr ⟨leaf, hleaf⟩
  · exact (leaf.clause_eq_some_falsified_iff hleaf.2 y).mpr
      ((P.verifier o).reachedLeaf_matches y)

theorem acceptingClauseTree_complete
    (P : SearchProblem M) (o : P.Output) (y : Fin M → F2)
    (h : P.valid y o) :
    ∃ D, (P.acceptingClauseTree o).eval y = some D := by
  let leaf := (P.verifier o).reachedLeaf y
  have hmatches : leaf.Matches y := (P.verifier o).reachedLeaf_matches y
  have hvalue : leaf.value = true :=
    (DecisionTree.eval_eq_leafValue_of_matches leaf hmatches).symm.trans
      ((P.verifier_correct y o).mpr h)
  have hsome : leaf.clause ≠ none := by
    intro hnone
    exact leaf.leafPartialAssignment_ne_none_of_matches hmatches
      ((DecisionTree.LeafPath.clause_eq_none_iff leaf).mp hnone)
  cases hclause : leaf.clause with
  | none => exact (hsome hclause).elim
  | some D =>
      exact ⟨D, by simp [acceptingClauseTree, leaf, hvalue, hclause]⟩

theorem acceptingClauseTree_mem_toCNF
    (P : SearchProblem M) (o : P.Output) (y : Fin M → F2) {D : Clause M}
    (h : (P.acceptingClauseTree o).eval y = some D) :
    D ∈ P.toCNF :=
  (P.mem_toCNF_iff).mpr ⟨o, (P.acceptingClauseTree_sound o y h).1⟩

end SearchProblem

end Revres
