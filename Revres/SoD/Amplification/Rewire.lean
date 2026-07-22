import Revres.SoD.Amplification.Growth

/-!
# Rewiring invariance

Redirect active bottom-row sources between designated null exit corners and
prove that clean conical-junta terms cannot observe the redirection.
-/

namespace Revres

open Lemma53

namespace SoD

namespace Amplification

variable {ell : ℕ}

namespace DecisionTree

universe u v

/-- Every query in a tree belongs to `S`. -/
def QueriesOnly {N : ℕ} {α : Type u}
    (T : DecisionTree N α) (S : Finset (Fin N)) : Prop :=
  match T with
  | .leaf _ => True
  | .query i zeroTree oneTree =>
      i ∈ S ∧ QueriesOnly zeroTree S ∧ QueriesOnly oneTree S

namespace QueriesOnly

theorem queriedVars_subset {N : ℕ} {α : Type u}
    {T : DecisionTree N α} {S : Finset (Fin N)}
    (h : QueriesOnly T S) (path : T.LeafPath) : path.queriedVars ⊆ S := by
  induction path with
  | leaf => simp
  | zero path ih =>
      exact Finset.insert_subset h.1 (ih h.2.1)
  | one path ih =>
      exact Finset.insert_subset h.1 (ih h.2.2)

theorem mono {N : ℕ} {α : Type u} {T : DecisionTree N α}
    {S U : Finset (Fin N)} (h : QueriesOnly T S) (hSU : S ⊆ U) :
    QueriesOnly T U := by
  induction T with
  | leaf => trivial
  | query i zeroTree oneTree ihzero ihone =>
      exact ⟨hSU h.1, ihzero h.2.1, ihone h.2.2⟩

theorem map_tree {N : ℕ} {α : Type u} {β : Type v}
    {T : DecisionTree N α} {S : Finset (Fin N)}
    (h : QueriesOnly T S) (f : α → β) : QueriesOnly (T.map f) S := by
  induction T with
  | leaf => trivial
  | query i zeroTree oneTree ihzero ihone =>
      exact ⟨h.1, ihzero h.2.1, ihone h.2.2⟩

end QueriesOnly

theorem readTuple_queriesOnly {N k : ℕ} (index : Fin k → Fin N) :
    QueriesOnly (DecisionTree.readTuple index) (Finset.univ.image index) := by
  induction k with
  | zero => simp [DecisionTree.readTuple, QueriesOnly]
  | succ k ih =>
      let tail := fun i : Fin k => index i.succ
      have htail := ih tail
      have hsubset : Finset.univ.image tail ⊆ Finset.univ.image index := by
        intro i hi
        obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_image.mpr ⟨b.succ, Finset.mem_univ _, rfl⟩
      have htail' := QueriesOnly.mono htail hsubset
      refine ⟨Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · exact QueriesOnly.map_tree (β := Fin (k + 1) → Lemma53.F2) htail'
          (@Fin.cons k (fun _ => Lemma53.F2) 0)
      · exact QueriesOnly.map_tree (β := Fin (k + 1) → Lemma53.F2) htail'
          (@Fin.cons k (fun _ => Lemma53.F2) 1)

theorem readSuccessor_queriesOnly {width : ℕ}
    (u : GridNode (BinaryPointer.order width)) :
    QueriesOnly (Encoding.readSuccessor u) (Encoding.nodeBits width u) := by
  simpa [Encoding.readSuccessor, BinaryPointer.read, Encoding.nodeBits] using
    QueriesOnly.map_tree
      (readTuple_queriesOnly (Encoding.successorBit (ell := width) u))
      BinaryPointer.decode

theorem queriedVars_reachedLeaf_bind_subset
    {N : ℕ} {α : Type u} {β : Type v}
    {T : DecisionTree N α} {next : α → DecisionTree N β}
    {x : Fin N → Lemma53.F2} {S U : Finset (Fin N)}
    (hT : QueriesOnly T S)
    (hnext : QueriesOnly (next (T.eval x)) U) :
    ((T.bind next).reachedLeaf x).queriedVars ⊆ S ∪ U := by
  induction T with
  | leaf a =>
      exact (QueriesOnly.queriedVars_subset hnext ((next a).reachedLeaf x)).trans
        (Finset.subset_union_right)
  | query i zeroTree oneTree ihzero ihone =>
      rcases hT with ⟨hi, hzero, hone⟩
      by_cases hxi : x i = 0
      · simp only [DecisionTree.bind, DecisionTree.reachedLeaf, hxi, if_pos,
          DecisionTree.LeafPath.queriedVars]
        apply Finset.insert_subset
        · exact Finset.mem_union_left _ hi
        · apply ihzero hzero
          simpa [DecisionTree.eval, hxi] using hnext
      · simp only [DecisionTree.bind, DecisionTree.reachedLeaf, hxi]
        apply Finset.insert_subset
        · exact Finset.mem_union_left _ hi
        · apply ihone hone
          simpa [DecisionTree.eval, hxi] using hnext

end DecisionTree

namespace Term

theorem Matches.agree_on_support {N : ℕ} {t : Term N}
    {x y : Fin N → Lemma53.F2} (hx : t.Matches x) (hy : t.Matches y) :
    ∀ i ∈ t.support, x i = y i := by
  intro i hi
  cases hval : t.val i with
  | none => exact (Term.mem_support.mp hi hval).elim
  | some b => exact (hx i b hval).trans (hy i b hval).symm

theorem witnesses_of_matches_imp_falsified {N : ℕ} {t : Term N} {C : Clause N}
    (h : ∀ z, t.Matches z → C.Falsified z) : t.Witnesses C := by
  intro i b hiC
  have hisupport : i ∈ t.support :=
    Clause.support_subset_term_support_of_matches_imp_falsified h (by simp [hiC])
  cases hval : t.val i with
  | none => exact (Term.mem_support.mp hisupport hval).elim
  | some c =>
      have hc := t.matches_completion i c hval
      have hb := h t.completion t.matches_completion i b hiC
      have hcb : c = b := hc.symm.trans hb
      exact congrArg some hcb

/-- Fully fixed adjacent source and null target records contain the canonical
proper-sink clause reached by the SoD verifier. -/
theorem witnessesFormula_of_fixes_properSink
    {width : ℕ} (hwidth : 0 < width)
    {t : Term (Encoding.variableCount width)}
    {source target : GridNode (BinaryPointer.order width)}
    (hnext : source.NextRow target)
    (hsource : t.FixesSuccessor source (some target.column))
    (htarget : t.FixesSuccessor target none) :
    t.WitnessesFormula (Encoding.searchCNF width hwidth) := by
  let x := t.completion
  have hu : source.IsInternal := GridNode.nextRow_internal hnext
  have htarget_eq : source.next hu target.column = target :=
    GridNode.eq_next_of_nextRow hnext
  have hsource_decode : (Encoding.decodeInput x).successor source =
      some target.column :=
    hsource.matches_decodeInput t.matches_completion
  have htarget_decode : (Encoding.decodeInput x).successor target = none :=
    htarget.matches_decodeInput t.matches_completion
  have hvalid : SoD.Valid (BinaryPointer.order_pos hwidth) (Encoding.decodeInput x)
      (.properSink source) := by
    refine ⟨target, ⟨hnext, hsource_decode⟩, ?_⟩
    rw [SoD.Input.Active, htarget_decode]
    simp
  have heval : (Encoding.verifier hwidth (.properSink source)).eval x = true :=
    (Encoding.verifier_correct hwidth (.properSink source) x).mpr hvalid
  let leaf := (Encoding.verifier hwidth (.properSink source)).reachedLeaf x
  have hleaf_matches : leaf.Matches x :=
    (Encoding.verifier hwidth (.properSink source)).reachedLeaf_matches x
  have hleaf_value : leaf.value = true :=
    (DecisionTree.eval_eq_leafValue_of_matches leaf hleaf_matches).symm.trans heval
  let nextTree := fun pointer : Option (Fin (BinaryPointer.order width)) =>
    match pointer with
    | none => DecisionTree.leaf false
    | some column =>
        (Encoding.readSuccessor (source.next hu column)).map
          fun nextPointer => decide (nextPointer = none)
  have hsource_eval : (Encoding.readSuccessor source).eval x = some target.column := by
    simpa using hsource_decode
  have hnext_queries : DecisionTree.QueriesOnly
      (nextTree ((Encoding.readSuccessor source).eval x))
      (Encoding.nodeBits width target) := by
    rw [hsource_eval]
    simp only [nextTree]
    rw [htarget_eq]
    exact
      DecisionTree.QueriesOnly.map_tree
        (DecisionTree.readSuccessor_queriesOnly target)
        (fun nextPointer => decide (nextPointer = none))
  have hqueries : leaf.queriedVars ⊆
      Encoding.nodeBits width source ∪ Encoding.nodeBits width target := by
    have hbind := DecisionTree.queriedVars_reachedLeaf_bind_subset
      (x := x)
      (DecisionTree.readSuccessor_queriesOnly source)
      hnext_queries
    have hverifier : Encoding.verifier hwidth (.properSink source) =
        (Encoding.readSuccessor source).bind nextTree := by
      simp only [Encoding.verifier, dif_pos hu, nextTree]
      rfl
    dsimp only [leaf]
    rw [hverifier]
    exact hbind
  have hsome : DecisionTree.leafPartialAssignment leaf ≠ none :=
    leaf.leafPartialAssignment_ne_none_of_matches hleaf_matches
  cases hclause : leaf.clause with
  | none =>
      exact (hsome ((DecisionTree.LeafPath.clause_eq_none_iff leaf).mp hclause)).elim
  | some C =>
      refine ⟨C, ?_, ?_⟩
      · apply (Encoding.searchProblem width hwidth).mem_toCNF_iff.mpr
        refine ⟨.properSink source, ?_⟩
        exact (Encoding.searchProblem width hwidth).mem_outputClauses_iff.mpr
          ⟨leaf, hleaf_value, hclause⟩
      · apply witnesses_of_matches_imp_falsified
        intro z hz
        apply (leaf.clause_eq_some_falsified_iff hclause z).mpr
        apply leaf.matches_of_agrees_on_variables hleaf_matches
        intro i hi
        rcases Finset.mem_union.mp (hqueries hi) with hisource | hitarget
        · exact Matches.agree_on_support hz t.matches_completion i
            (hsource.nodeBits_subset_support hisource)
        · exact Matches.agree_on_support hz t.matches_completion i
            (htarget.nodeBits_subset_support hitarget)

theorem witnesses_cleaningFormula_of_fixes_properSink
    {hell : 0 < ell}
    {t : Term (Encoding.variableCount (2 * ell))}
    {source target : GridNode (ActiveEdge.ambientOrder ell)}
    (hnext : source.NextRow target)
    (hsource : t.FixesSuccessor source (some target.column))
    (htarget : t.FixesSuccessor target none) :
    t.WitnessesFormula (Preprocess.cleaningFormula hell) := by
  exact witnessesFormula_of_fixes_properSink
    (ActiveEdge.ambientWidth_pos hell) hnext hsource htarget

theorem NodeAligned.fixesSuccessor_of_readsNode_of_matches
    {width : ℕ} {t : Term (Encoding.variableCount width)}
    (haligned : t.NodeAligned)
    {u : GridNode (BinaryPointer.order width)}
    (hread : t.ReadsNode u)
    {z : Fin (Encoding.variableCount width) → Lemma53.F2}
    (hmatch : t.Matches z) :
    t.FixesSuccessor u ((Encoding.decodeInput z).successor u) := by
  obtain ⟨pointer, hfix⟩ := haligned.exists_fixesSuccessor_of_readsNode hread
  have hpointer := hfix.matches_decodeInput hmatch
  rw [hpointer]
  exact hfix

theorem fixesSuccessor_of_nodeBits_subset_support_of_matches
    {width : ℕ} {t : Term (Encoding.variableCount width)}
    {u : GridNode (BinaryPointer.order width)}
    {z : Fin (Encoding.variableCount width) → Lemma53.F2}
    (hbits : Encoding.nodeBits width u ⊆ t.support)
    (hmatch : t.Matches z) :
    t.FixesSuccessor u ((Encoding.decodeInput z).successor u) := by
  intro b
  rw [Encoding.decodeInput_successor, BinaryPointer.encode_decode]
  have hi : Encoding.successorBit u b ∈ t.support :=
    hbits (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  have hne := Term.mem_support.mp hi
  cases hval : t.val (Encoding.successorBit u b) with
  | none => exact (hne hval).elim
  | some c => exact congrArg some (hmatch _ c hval).symm

end Term

/-- Redirect exactly the listed source records to one target column. -/
def redirectInput (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target : GridNode (ActiveEdge.ambientOrder ell)) :
    SoD.Input (ActiveEdge.ambientOrder ell) where
  successor u := if u ∈ sources then some target.column else x.successor u

@[simp]
theorem redirectInput_successor_of_mem
    (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target u : GridNode (ActiveEdge.ambientOrder ell)) (hu : u ∈ sources) :
    (redirectInput x sources target).successor u = some target.column := by
  simp [redirectInput, hu]

@[simp]
theorem redirectInput_successor_of_not_mem
    (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target u : GridNode (ActiveEdge.ambientOrder ell)) (hu : u ∉ sources) :
    (redirectInput x sources target).successor u = x.successor u := by
  simp [redirectInput, hu]

/-- Canonical encoding of a redirected semantic input. -/
noncomputable def redirectedAssignment
    (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target : GridNode (ActiveEdge.ambientOrder ell)) :
    Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2 :=
  Encoding.encodeInput (redirectInput x sources target)

@[simp]
theorem redirectedAssignment_successorBit_of_mem
    (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target u : GridNode (ActiveEdge.ambientOrder ell)) (hu : u ∈ sources)
    (b : Fin (2 * ell)) :
    redirectedAssignment x sources target (Encoding.successorBit u b) =
      BinaryPointer.encode (some target.column) b := by
  simp [redirectedAssignment, hu]

@[simp]
theorem redirectedAssignment_successorBit_of_not_mem
    (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target u : GridNode (ActiveEdge.ambientOrder ell)) (hu : u ∉ sources)
    (b : Fin (2 * ell)) :
    redirectedAssignment x sources target (Encoding.successorBit u b) =
      Encoding.encodeInput x (Encoding.successorBit u b) := by
  simp [redirectedAssignment, hu]

theorem redirectedAssignment_eq_original_of_node_not_mem
    (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target : GridNode (ActiveEdge.ambientOrder ell))
    {i : Fin (Encoding.variableCount (2 * ell))}
    (hi : Encoding.nodeOfBit (2 * ell) i ∉ sources) :
    redirectedAssignment x sources target i = Encoding.encodeInput x i := by
  simp only [redirectedAssignment, Encoding.encodeInput]
  have hi' : ((Encoding.bitIndexEquiv (2 * ell)).symm i).1 ∉ sources := by
    simpa [Encoding.nodeOfBit] using hi
  rw [redirectInput_successor_of_not_mem x sources target _ hi']

theorem node_mem_of_redirectedAssignment_ne
    (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (sources : Finset (GridNode (ActiveEdge.ambientOrder ell)))
    (target : GridNode (ActiveEdge.ambientOrder ell))
    {i : Fin (Encoding.variableCount (2 * ell))}
    (hne : redirectedAssignment x sources target i ≠ Encoding.encodeInput x i) :
    Encoding.nodeOfBit (2 * ell) i ∈ sources := by
  by_contra hi
  exact hne (redirectedAssignment_eq_original_of_node_not_mem x sources target hi)

/-- The exact semantic hypotheses required by exit-blindness. -/
structure RewireSpec (ell : ℕ) (hell : 0 < ell) where
  before : SoD.Input (ActiveEdge.ambientOrder ell)
  sources : Finset (GridNode (ActiveEdge.ambientOrder ell))
  oldExit : GridNode (ActiveEdge.ambientOrder ell)
  newExit : GridNode (ActiveEdge.ambientOrder ell)
  source_old_designated :
    ∀ u ∈ sources, Preprocess.IsDesignatedExit hell u oldExit
  source_new_designated :
    ∀ u ∈ sources, Preprocess.IsDesignatedExit hell u newExit
  source_points_old : ∀ u ∈ sources, before.successor u = some oldExit.column
  oldExit_null : before.successor oldExit = none
  newExit_null : before.successor newExit = none

namespace RewireSpec

variable {hell : 0 < ell}

def after (rw : RewireSpec ell hell) : SoD.Input (ActiveEdge.ambientOrder ell) :=
  redirectInput rw.before rw.sources rw.newExit

noncomputable def beforeAssignment (rw : RewireSpec ell hell) :
    Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2 :=
  Encoding.encodeInput rw.before

noncomputable def afterAssignment (rw : RewireSpec ell hell) :
    Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2 :=
  Encoding.encodeInput rw.after

theorem source_points_new (rw : RewireSpec ell hell) {u} (hu : u ∈ rw.sources) :
    rw.after.successor u = some rw.newExit.column := by
  exact redirectInput_successor_of_mem rw.before rw.sources rw.newExit u hu

theorem successor_eq_of_not_mem (rw : RewireSpec ell hell) {u} (hu : u ∉ rw.sources) :
    rw.after.successor u = rw.before.successor u := by
  exact redirectInput_successor_of_not_mem rw.before rw.sources rw.newExit u hu

theorem oldExit_not_mem (rw : RewireSpec ell hell) : rw.oldExit ∉ rw.sources := by
  intro hmem
  have hnext := (rw.source_old_designated rw.oldExit hmem).source_nextRow_target
  exact (GridNode.nextRow_ne hnext) rfl

theorem newExit_not_mem (rw : RewireSpec ell hell) : rw.newExit ∉ rw.sources := by
  intro hmem
  have hnext := (rw.source_new_designated rw.newExit hmem).source_nextRow_target
  exact (GridNode.nextRow_ne hnext) rfl

theorem after_oldExit_null (rw : RewireSpec ell hell) :
    rw.after.successor rw.oldExit = none := by
  rw [rw.successor_eq_of_not_mem rw.oldExit_not_mem]
  exact rw.oldExit_null

theorem after_newExit_null (rw : RewireSpec ell hell) :
    rw.after.successor rw.newExit = none := by
  rw [rw.successor_eq_of_not_mem rw.newExit_not_mem]
  exact rw.newExit_null

theorem node_mem_of_assignments_ne (rw : RewireSpec ell hell)
    {i : Fin (Encoding.variableCount (2 * ell))}
    (hne : rw.afterAssignment i ≠ rw.beforeAssignment i) :
    Encoding.nodeOfBit (2 * ell) i ∈ rw.sources := by
  exact node_mem_of_redirectedAssignment_ne rw.before rw.sources rw.newExit hne

end RewireSpec

theorem term_indicator_rewire_eq
    {hell : 0 < ell} (rw : RewireSpec ell hell)
    {t : Term (Encoding.variableCount (2 * ell))}
    (htAlign : t.NodeAligned)
    (htCurious : t.ExitCurious hell)
    (htNonWitness : ¬t.WitnessesFormula (Preprocess.cleaningFormula hell)) :
    t.indicator rw.beforeAssignment = t.indicator rw.afterAssignment := by
  classical
  by_cases hbefore : t.Matches rw.beforeAssignment
  · by_cases hafter : t.Matches rw.afterAssignment
    · simp [Term.indicator, hbefore, hafter]
    · rw [Term.Matches] at hafter
      push Not at hafter
      obtain ⟨i, b, hib, hfail⟩ := hafter
      have hbefore_i : rw.beforeAssignment i = b := hbefore i b hib
      have hchanged : rw.afterAssignment i ≠ rw.beforeAssignment i := by
        intro heq
        exact hfail (heq.trans hbefore_i)
      let source := Encoding.nodeOfBit (2 * ell) i
      have hsource_mem : source ∈ rw.sources :=
        rw.node_mem_of_assignments_ne hchanged
      have hread : t.ReadsNode source := by
        refine ⟨i, Term.mem_support.mpr ?_, Encoding.mem_nodeBits_iff.mpr rfl⟩
        simp [hib]
      have hsource_fix_actual :=
        Term.NodeAligned.fixesSuccessor_of_readsNode_of_matches
          htAlign hread hbefore
      have hsource_fix : t.FixesSuccessor source (some rw.oldExit.column) := by
        simpa [RewireSpec.beforeAssignment,
          rw.source_points_old source hsource_mem] using hsource_fix_actual
      have hexit := rw.source_old_designated source hsource_mem
      have htarget_bits : Encoding.nodeBits (2 * ell) rw.oldExit ⊆ t.support :=
        htCurious source rw.oldExit hexit hsource_fix
      have htarget_fix_actual :=
        Term.fixesSuccessor_of_nodeBits_subset_support_of_matches
          htarget_bits hbefore
      have htarget_fix : t.FixesSuccessor rw.oldExit none := by
        simpa [RewireSpec.beforeAssignment, rw.oldExit_null] using htarget_fix_actual
      exact (htNonWitness
        (Term.witnesses_cleaningFormula_of_fixes_properSink
          hexit.source_nextRow_target hsource_fix htarget_fix)).elim
  · by_cases hafter : t.Matches rw.afterAssignment
    · rw [Term.Matches] at hbefore
      push Not at hbefore
      obtain ⟨i, b, hib, hfail⟩ := hbefore
      have hafter_i : rw.afterAssignment i = b := hafter i b hib
      have hchanged : rw.afterAssignment i ≠ rw.beforeAssignment i := by
        intro heq
        exact hfail (heq.symm.trans hafter_i)
      let source := Encoding.nodeOfBit (2 * ell) i
      have hsource_mem : source ∈ rw.sources :=
        rw.node_mem_of_assignments_ne hchanged
      have hread : t.ReadsNode source := by
        refine ⟨i, Term.mem_support.mpr ?_, Encoding.mem_nodeBits_iff.mpr rfl⟩
        simp [hib]
      have hsource_fix_actual :=
        Term.NodeAligned.fixesSuccessor_of_readsNode_of_matches
          htAlign hread hafter
      have hsource_fix_semantic :
          t.FixesSuccessor source (rw.after.successor source) := by
        simpa only [RewireSpec.afterAssignment, Encoding.decodeInput_encodeInput] using
          hsource_fix_actual
      have hsource_fix : t.FixesSuccessor source (some rw.newExit.column) := by
        rw [rw.source_points_new hsource_mem] at hsource_fix_semantic
        exact hsource_fix_semantic
      have hexit := rw.source_new_designated source hsource_mem
      have htarget_bits : Encoding.nodeBits (2 * ell) rw.newExit ⊆ t.support :=
        htCurious source rw.newExit hexit hsource_fix
      have htarget_fix_actual :=
        Term.fixesSuccessor_of_nodeBits_subset_support_of_matches
          htarget_bits hafter
      have htarget_fix : t.FixesSuccessor rw.newExit none := by
        simpa [RewireSpec.afterAssignment, rw.after_newExit_null] using
          htarget_fix_actual
      exact (htNonWitness
        (Term.witnesses_cleaningFormula_of_fixes_properSink
          hexit.source_nextRow_target hsource_fix htarget_fix)).elim
    · simp [Term.indicator, hbefore, hafter]

theorem JuntaRep.eval_rewire_eq
    {hell : 0 < ell} (rw : RewireSpec ell hell)
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hAlign : JR.NodeAligned)
    (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell)) :
    JR.eval rw.beforeAssignment = JR.eval rw.afterAssignment := by
  classical
  rw [JuntaRep.eval, JuntaRep.eval, Finsupp.sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [term_indicator_rewire_eq rw (hAlign t ht) (hCurious t ht) (hNonWitness t ht)]

/-- Active embedded local last-row records whose pointers leave the current box. -/
noncomputable def activeLastSources
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (_hgood : GoodState hell JR s) (_hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2) :
    Finset (GridNode (ActiveEdge.ambientOrder ell)) := by
  classical
  exact (Finset.univ.filter fun u =>
    u.IsLastRow ∧ (SoPL.Encoding.decodeInput ell y).Active u).image
      (ActiveEdge.embedNode hell s.currentBox)

theorem mem_activeLastSources_iff
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {hgood : GoodState hell JR s} {hinternal : s.currentBox.IsInternal}
    {y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2}
    {source : GridNode (ActiveEdge.ambientOrder ell)} :
    source ∈ activeLastSources hgood hinternal y ↔
      ∃ u, u.IsLastRow ∧ (SoPL.Encoding.decodeInput ell y).Active u ∧
        source = ActiveEdge.embedNode hell s.currentBox u := by
  classical
  simp [activeLastSources, and_assoc, eq_comm]

/-- The semantic active-edge input underlying `stageAssignment`. -/
noncomputable def stageInput
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2) :
    SoD.Input (ActiveEdge.ambientOrder ell) :=
  ActiveEdge.activeEdgeEmbedding (hgood.toStageContext hinternal)
    (SoPL.Encoding.decodeInput ell y)

@[simp]
theorem encodeInput_stageInput_eq_stageAssignment
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2) :
    Encoding.encodeInput (stageInput hgood hinternal y) =
      stageAssignment hgood hinternal y :=
  rfl

theorem stageInput_source_points_parking
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    {source : GridNode (ActiveEdge.ambientOrder ell)}
    (hsource : source ∈ activeLastSources hgood hinternal y) :
    (stageInput hgood hinternal y).successor source =
      some (ActiveEdge.embeddedCorner hell
        (parkingExitBox hell s.currentBox hinternal)).column := by
  obtain ⟨u, hlast, hactive, rfl⟩ := mem_activeLastSources_iff.mp hsource
  simpa [stageInput, hactive] using
    ActiveEdge.activeEdgeEmbedding_last_successor
      (hgood.toStageContext hinternal) (SoPL.Encoding.decodeInput ell y) u hlast

theorem activeLastSource_designatedExit
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    {source : GridNode (ActiveEdge.ambientOrder ell)}
    (hsource : source ∈ activeLastSources hgood hinternal y)
    {R : GridNode (ActiveEdge.localOrder ell)} (hR : s.currentBox.NextRow R) :
    Preprocess.IsDesignatedExit hell source (ActiveEdge.embeddedCorner hell R) := by
  obtain ⟨u, hlast, _hactive, rfl⟩ := mem_activeLastSources_iff.mp hsource
  exact ⟨s.currentBox, R, u, hlast, hR, rfl, rfl⟩

theorem stageInput_corner_null_of_nextRow
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    {R : GridNode (ActiveEdge.localOrder ell)} (hR : s.currentBox.NextRow R) :
    (stageInput hgood hinternal y).successor
      (ActiveEdge.embeddedCorner hell R) = none := by
  have hne : s.currentBox ≠ R := GridNode.nextRow_ne hR
  have houtside : ActiveEdge.embeddedCorner hell R ∉
      ActiveEdge.embeddedSubgrid hell s.currentBox := by
    intro hmem
    exact (Finset.disjoint_left.mp (ActiveEdge.embeddedSubgrid_disjoint hne))
      hmem (ActiveEdge.embeddedCorner_mem hell R)
  have hbase := ActiveEdge.activeEdgeEmbedding_outside
    (hgood.toStageContext hinternal) (SoPL.Encoding.decodeInput ell y) houtside
  rw [stageInput, hbase]
  apply hgood.structural.later_null R
  · unfold GridNode.NextRow at hR
    omega

/-- Redirect the active embedded last-row records to candidate box `R`. -/
noncomputable def rewiredStageInput
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (_hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    SoD.Input (ActiveEdge.ambientOrder ell) :=
  redirectInput (stageInput hgood hinternal y)
    (activeLastSources hgood hinternal y) (ActiveEdge.embeddedCorner hell R)

/-- Canonical encoding of the candidate-rewired stage input. -/
noncomputable def rewiredStageAssignment
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2 :=
  Encoding.encodeInput (rewiredStageInput hgood hinternal y R hR)

/-- The active-edge stage satisfies the abstract before/after rewiring contract. -/
noncomputable def stageRewireSpec
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    RewireSpec ell hell where
  before := stageInput hgood hinternal y
  sources := activeLastSources hgood hinternal y
  oldExit := ActiveEdge.embeddedCorner hell
    (parkingExitBox hell s.currentBox hinternal)
  newExit := ActiveEdge.embeddedCorner hell R
  source_old_designated := by
    intro source hsource
    exact activeLastSource_designatedExit hgood hinternal y hsource
      (parkingExitBox_nextRow hell s.currentBox hinternal)
  source_new_designated := by
    intro source hsource
    exact activeLastSource_designatedExit hgood hinternal y hsource
      (SoD.nextCandidate_nextRow hR)
  source_points_old := by
    intro source hsource
    exact stageInput_source_points_parking hgood hinternal y hsource
  oldExit_null := stageInput_corner_null_of_nextRow hgood hinternal y
    (parkingExitBox_nextRow hell s.currentBox hinternal)
  newExit_null := stageInput_corner_null_of_nextRow hgood hinternal y
    (SoD.nextCandidate_nextRow hR)

@[simp]
theorem stageRewireSpec_beforeAssignment
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (stageRewireSpec hgood hinternal y R hR).beforeAssignment =
      stageAssignment hgood hinternal y :=
  rfl

@[simp]
theorem stageRewireSpec_afterAssignment
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (stageRewireSpec hgood hinternal y R hR).afterAssignment =
      rewiredStageAssignment hgood hinternal y R hR :=
  rfl

theorem term_indicator_stage_rewire_eq
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    {t : Term (Encoding.variableCount (2 * ell))}
    (htAlign : t.NodeAligned) (htCurious : t.ExitCurious hell)
    (htNonWitness : ¬t.WitnessesFormula (Preprocess.cleaningFormula hell)) :
    t.indicator (stageAssignment hgood hinternal y) =
      t.indicator (rewiredStageAssignment hgood hinternal y R hR) := by
  exact term_indicator_rewire_eq (stageRewireSpec hgood hinternal y R hR)
    htAlign htCurious htNonWitness

theorem JuntaRep.eval_stage_rewire_eq
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell)) :
    JR.eval (stageAssignment hgood hinternal y) =
      JR.eval (rewiredStageAssignment hgood hinternal y R hR) := by
  exact JuntaRep.eval_rewire_eq (stageRewireSpec hgood hinternal y R hR)
    hAlign hCurious hNonWitness

theorem one_add_eval_rewired_gt_of_stage_gt
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    {K : ℝ}
    (hgrowth : K < 1 + JR.eval (stageAssignment hgood hinternal y)) :
    K < 1 + JR.eval (rewiredStageAssignment hgood hinternal y R hR) := by
  rw [← JuntaRep.eval_stage_rewire_eq hgood hinternal y R hR
    hAlign hCurious hNonWitness]
  exact hgrowth

end Amplification

end SoD

end Revres
