import Revres.CNF.Formula
import Revres.DecisionTree.Basic
import Mathlib.Data.Finset.Union

/-!
# Canonical CNFs for finite total search problems

Each reachable accepting leaf of an output verifier contributes its falsifying cube as an ordinary
clause. Identical clauses are deduplicated by `Finset`; a fixed producing output is then chosen as
the clause label.
-/

namespace Revres

open Lemma53

/-- A finite total search problem with one Boolean decision-tree verifier per output. -/
structure SearchProblem (N : ℕ) where
  Output : Type
  instOutputFintype : Fintype Output
  valid : (Fin N → F2) → Output → Prop
  total : ∀ x, ∃ o, valid x o
  verifier : Output → DecisionTree N Bool
  verifier_correct : ∀ x o, (verifier o).eval x = true ↔ valid x o

attribute [instance] SearchProblem.instOutputFintype

namespace DecisionTree

namespace LeafPath

variable {N : ℕ} {α : Type*} {T : DecisionTree N α}

/-- The clause of a reachable leaf cube; contradictory paths contribute no clause. -/
noncomputable def clause (leaf : T.LeafPath) : Option (Clause N) :=
  match DecisionTree.leafPartialAssignment leaf with
  | none => none
  | some term => some term.val

theorem clause_eq_some_falsified_iff
    (leaf : T.LeafPath) {C : Clause N}
    (hC : leaf.clause = some C) (x : Fin N → F2) :
    C.Falsified x ↔ leaf.Matches x := by
  cases hterm : DecisionTree.leafPartialAssignment leaf with
  | none => simp [clause, hterm] at hC
  | some term =>
      have hCterm : term.val = C := by
        simpa [clause, hterm] using hC
      subst C
      exact (leaf.matches_iff_of_leafPartialAssignment_eq_some hterm x).symm

@[simp]
theorem clause_eq_none_iff (leaf : T.LeafPath) :
    leaf.clause = none ↔ DecisionTree.leafPartialAssignment leaf = none := by
  cases hterm : DecisionTree.leafPartialAssignment leaf <;> simp [clause, hterm]

private theorem queriedVars_card_le_length (leaf : T.LeafPath) :
    leaf.queriedVars.card ≤ leaf.length := by
  induction leaf with
  | leaf => simp
  | @zero i zeroTree oneTree leaf ih =>
      change (insert i leaf.queriedVars).card ≤ 1 + leaf.length
      exact (Finset.card_insert_le i leaf.queriedVars).trans_eq (Nat.add_comm _ _)
        |>.trans (Nat.add_le_add_left ih 1)
  | @one i zeroTree oneTree leaf ih =>
      change (insert i leaf.queriedVars).card ≤ 1 + leaf.length
      exact (Finset.card_insert_le i leaf.queriedVars).trans_eq (Nat.add_comm _ _)
        |>.trans (Nat.add_le_add_left ih 1)

theorem width_clause_le_length
    (leaf : T.LeafPath) {C : Clause N} (hC : leaf.clause = some C) :
    C.width ≤ leaf.length := by
  cases hterm : DecisionTree.leafPartialAssignment leaf with
  | none => simp [clause, hterm] at hC
  | some term =>
      have hCterm : term.val = C := by
        simpa [clause, hterm] using hC
      subst C
      change term.support.card ≤ leaf.length
      rw [leaf.support_of_leafPartialAssignment_eq_some hterm]
      exact queriedVars_card_le_length leaf

end LeafPath

end DecisionTree

namespace SearchProblem

variable {N : ℕ}

/-- Clauses contributed by the reachable accepting leaves of one output verifier. -/
noncomputable def outputClauses (P : SearchProblem N) (o : P.Output) : CNF N := by
  classical
  exact Finset.univ.biUnion fun leaf : (P.verifier o).LeafPath =>
    if leaf.value = true then
      match leaf.clause with
      | none => ∅
      | some C => {C}
    else
      ∅

theorem mem_outputClauses_iff
    (P : SearchProblem N) {o : P.Output} {C : Clause N} :
    C ∈ P.outputClauses o ↔
      ∃ leaf : (P.verifier o).LeafPath,
        leaf.value = true ∧ leaf.clause = some C := by
  classical
  simp only [outputClauses, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨leaf, hleaf⟩
    by_cases hvalue : leaf.value = true
    · cases hclause : leaf.clause with
      | none => simp [hvalue, hclause] at hleaf
      | some D =>
          have hCD : C = D := by simpa [hvalue, hclause] using hleaf
          have hDC : D = C := hCD.symm
          subst D
          exact ⟨leaf, hvalue, hclause⟩
    · simp [hvalue] at hleaf
  · rintro ⟨leaf, hvalue, hclause⟩
    refine ⟨leaf, ?_⟩
    simp [hvalue, hclause]

theorem exists_falsified_mem_outputClauses_iff
    (P : SearchProblem N) (o : P.Output) (x : Fin N → F2) :
    (∃ C ∈ P.outputClauses o, C.Falsified x) ↔ P.valid x o := by
  constructor
  · rintro ⟨C, hCmem, hCfalsified⟩
    obtain ⟨leaf, hvalue, hclause⟩ := (P.mem_outputClauses_iff).mp hCmem
    have hmatches : leaf.Matches x :=
      (leaf.clause_eq_some_falsified_iff hclause x).mp hCfalsified
    apply (P.verifier_correct x o).mp
    calc
      (P.verifier o).eval x = leaf.value :=
        DecisionTree.eval_eq_leafValue_of_matches leaf hmatches
      _ = true := hvalue
  · intro hvalid
    let leaf := (P.verifier o).reachedLeaf x
    have hmatches : leaf.Matches x := (P.verifier o).reachedLeaf_matches x
    have hvalue : leaf.value = true :=
      (DecisionTree.eval_eq_leafValue_of_matches leaf hmatches).symm.trans
        ((P.verifier_correct x o).mpr hvalid)
    have hsome : DecisionTree.leafPartialAssignment leaf ≠ none :=
      leaf.leafPartialAssignment_ne_none_of_matches hmatches
    cases hterm : DecisionTree.leafPartialAssignment leaf with
    | none => exact (hsome hterm).elim
    | some term =>
        refine ⟨term.val, (P.mem_outputClauses_iff).mpr ⟨leaf, hvalue, ?_⟩, ?_⟩
        · simp [DecisionTree.LeafPath.clause, hterm]
        · exact (leaf.matches_iff_of_leafPartialAssignment_eq_some hterm x).mp hmatches

/-- The canonical CNF obtained by taking the union of all output clause families. -/
noncomputable def toCNF (P : SearchProblem N) : CNF N := by
  classical
  exact Finset.univ.biUnion P.outputClauses

theorem mem_toCNF_iff (P : SearchProblem N) {C : Clause N} :
    C ∈ P.toCNF ↔ ∃ o : P.Output, C ∈ P.outputClauses o := by
  classical
  simp [toCNF]

/-- A fixed producing output for a clause of the deduplicated canonical CNF. -/
noncomputable def clauseOutput (P : SearchProblem N) (C : ↑P.toCNF) : P.Output :=
  Classical.choose ((P.mem_toCNF_iff).mp C.2)

theorem clauseOutput_mem (P : SearchProblem N) (C : ↑P.toCNF) :
    C.1 ∈ P.outputClauses (P.clauseOutput C) :=
  Classical.choose_spec ((P.mem_toCNF_iff).mp C.2)

theorem clauseOutput_valid
    (P : SearchProblem N) (C : ↑P.toCNF) {x : Fin N → F2}
    (hC : C.1.Falsified x) :
    P.valid x (P.clauseOutput C) :=
  (P.exists_falsified_mem_outputClauses_iff (P.clauseOutput C) x).mp
    ⟨C.1, P.clauseOutput_mem C, hC⟩

theorem toCNF_unsat (P : SearchProblem N) : P.toCNF.Unsat := by
  intro x
  obtain ⟨o, hvalid⟩ := P.total x
  obtain ⟨C, hCmem, hCfalsified⟩ :=
    (P.exists_falsified_mem_outputClauses_iff o x).mpr hvalid
  exact ⟨C, (P.mem_toCNF_iff).mpr ⟨o, hCmem⟩, hCfalsified⟩

/-- The maximum decision-tree depth among all output verifiers. -/
noncomputable def verifierDepth (P : SearchProblem N) : ℕ :=
  Finset.univ.sup fun o : P.Output => (P.verifier o).depth

theorem verifier_depth_le (P : SearchProblem N) (o : P.Output) :
    (P.verifier o).depth ≤ P.verifierDepth := by
  classical
  exact Finset.le_sup (s := Finset.univ) (f := fun a => (P.verifier a).depth)
    (Finset.mem_univ o)

theorem clause_width_le_verifierDepth
    (P : SearchProblem N) {C : Clause N} (hC : C ∈ P.toCNF) :
    C.width ≤ P.verifierDepth := by
  obtain ⟨o, hCo⟩ := (P.mem_toCNF_iff).mp hC
  obtain ⟨leaf, _hvalue, hclause⟩ := (P.mem_outputClauses_iff).mp hCo
  exact (leaf.width_clause_le_length hclause).trans
    (leaf.length_le_depth.trans (P.verifier_depth_le o))

theorem toCNF_width_le_verifierDepth (P : SearchProblem N) :
    P.toCNF.width ≤ P.verifierDepth := by
  rw [CNF.width]
  exact Finset.sup_le fun C hC => P.clause_width_le_verifierDepth hC

end SearchProblem

end Revres
