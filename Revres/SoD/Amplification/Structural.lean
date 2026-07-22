import Revres.SoD.Amplification.Cleanup

/-!
# Structural amplification update

Turn a selected, rewired cleanup candidate into the next restriction and prove
that the path-family stage restores the complete amplification invariant.
-/

namespace Revres

open Lemma53

namespace SoD

namespace Amplification

variable {ell : ℕ}

namespace Restriction

/-- Keep `z` outside `S` and leave exactly the coordinates in `S` free. -/
def fromAssignmentOutside
    (S : Finset (Fin (Encoding.variableCount (2 * ell))))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    Restriction ell where
  val i := if i ∈ S then none else some (z i)

@[simp]
theorem fromAssignmentOutside_apply_of_mem
    (S : Finset (Fin (Encoding.variableCount (2 * ell))))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2)
    {i : Fin (Encoding.variableCount (2 * ell))} (hi : i ∈ S) :
    (fromAssignmentOutside S z).val i = none := by
  simp [fromAssignmentOutside, hi]

@[simp]
theorem fromAssignmentOutside_apply_of_not_mem
    (S : Finset (Fin (Encoding.variableCount (2 * ell))))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2)
    {i : Fin (Encoding.variableCount (2 * ell))} (hi : i ∉ S) :
    (fromAssignmentOutside S z).val i = some (z i) := by
  simp [fromAssignmentOutside, hi]

theorem fromAssignmentOutside_freeExactly
    (S : Finset (Fin (Encoding.variableCount (2 * ell))))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (fromAssignmentOutside S z).FreeExactly S := by
  intro i
  simp [fromAssignmentOutside]

theorem matches_fromAssignmentOutside_iff
    (S : Finset (Fin (Encoding.variableCount (2 * ell))))
    (z w : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (fromAssignmentOutside S z).Matches w ↔
      ∀ i, i ∉ S → w i = z i := by
  constructor
  · intro hmatch i hi
    exact hmatch i (z i) (by simp [fromAssignmentOutside, hi])
  · intro hagree i b hib
    by_cases hi : i ∈ S
    · simp [fromAssignmentOutside, hi] at hib
    · have hb : z i = b := by
        simpa [fromAssignmentOutside, hi] using hib
      exact (hagree i hi).trans hb

theorem nullAssignment_fromAssignmentOutside_eq
    (S : Finset (Fin (Encoding.variableCount (2 * ell))))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2)
    (hzero : ∀ i ∈ S, z i = 0) :
    (fromAssignmentOutside S z).nullAssignment = z := by
  funext i
  by_cases hi : i ∈ S
  · simp [Restriction.nullAssignment, Term.completion, fromAssignmentOutside,
      hi, hzero i hi]
  · simp [Restriction.nullAssignment, Term.completion, fromAssignmentOutside, hi]

end Restriction

namespace RewireSpec

variable {hell : 0 < ell}

/-- Redirecting a listed nonnull source to another target preserves activity. -/
theorem after_active_iff_before (rw : RewireSpec ell hell)
    (u : GridNode (ActiveEdge.ambientOrder ell)) :
    rw.after.Active u ↔ rw.before.Active u := by
  rw [SoD.Input.Active, SoD.Input.Active]
  by_cases hu : u ∈ rw.sources
  · rw [rw.source_points_new hu, rw.source_points_old u hu]
    simp
  · rw [rw.successor_eq_of_not_mem hu]

/-- At a source not redirected, proper-sink-witness status is unchanged. -/
theorem after_properSinkWitness_iff_before_of_not_mem
    (rw : RewireSpec ell hell)
    {u : GridNode (ActiveEdge.ambientOrder ell)} (hu : u ∉ rw.sources) :
    rw.after.ProperSinkWitness u ↔ rw.before.ProperSinkWitness u := by
  constructor
  · rintro ⟨v, ⟨hrow, hsuccessor⟩, hinactive⟩
    refine ⟨v, ⟨hrow, ?_⟩, ?_⟩
    · rwa [rw.successor_eq_of_not_mem hu] at hsuccessor
    · intro hactive
      exact hinactive ((rw.after_active_iff_before v).2 hactive)
  · rintro ⟨v, ⟨hrow, hsuccessor⟩, hinactive⟩
    refine ⟨v, ⟨hrow, ?_⟩, ?_⟩
    · rwa [rw.successor_eq_of_not_mem hu]
    · intro hactive
      exact hinactive ((rw.after_active_iff_before v).1 hactive)

end RewireSpec

theorem activeLastSource_mem_currentSubgrid
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {hgood : GoodState hell JR s} {hinternal : s.currentBox.IsInternal}
    {y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2}
    {source : GridNode (ActiveEdge.ambientOrder ell)}
    (hsource : source ∈ activeLastSources hgood hinternal y) :
    source ∈ ActiveEdge.embeddedSubgrid hell s.currentBox := by
  obtain ⟨u, _hlast, _hactive, rfl⟩ := mem_activeLastSources_iff.mp hsource
  exact ActiveEdge.mem_embeddedSubgrid_iff.mpr ⟨u, rfl⟩

/-- Rewiring inside the current box leaves every strictly later box null. -/
theorem rewiredStageInput_nullOnBox_of_current_row_lt
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    (S : GridNode (ActiveEdge.localOrder ell))
    (hrow : s.currentBox.row.val < S.row.val) :
    NullOnBox hell (rewiredStageInput hgood hinternal y R hR) S := by
  intro u
  have hne : s.currentBox ≠ S := by
    intro heq
    subst S
    omega
  have houtside : ActiveEdge.embedNode hell S u ∉
      ActiveEdge.embeddedSubgrid hell s.currentBox := by
    intro hcurrent
    exact (Finset.disjoint_left.mp (ActiveEdge.embeddedSubgrid_disjoint hne))
      hcurrent (ActiveEdge.mem_embeddedSubgrid_iff.mpr ⟨u, rfl⟩)
  have hnotsource : ActiveEdge.embedNode hell S u ∉
      activeLastSources hgood hinternal y := by
    intro hsource
    exact houtside (activeLastSource_mem_currentSubgrid hsource)
  rw [rewiredStageInput,
    redirectInput_successor_of_not_mem _ _ _ _ hnotsource]
  rw [stageInput, ActiveEdge.activeEdgeEmbedding_outside
    (hgood.toStageContext hinternal) (SoPL.Encoding.decodeInput ell y) houtside]
  exact hgood.structural.later_null S hrow u

theorem rewiredStageInput_nullOn_candidate
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    NullOnBox hell (rewiredStageInput hgood hinternal y R hR) R := by
  apply rewiredStageInput_nullOnBox_of_current_row_lt hgood hinternal y R hR R
  have hnext := SoD.nextCandidate_nextRow hR
  unfold GridNode.NextRow at hnext
  omega

theorem rewiredStageInput_nullAfter_candidate
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    NullAfter hell (rewiredStageInput hgood hinternal y R hR) R := by
  intro S hrow
  apply rewiredStageInput_nullOnBox_of_current_row_lt hgood hinternal y R hR S
  have hnext := SoD.nextCandidate_nextRow hR
  unfold GridNode.NextRow at hnext
  omega

theorem rewiredStageAssignment_eq_zero_of_mem_boxBits
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    {i : Fin (Encoding.variableCount (2 * ell))} (hi : i ∈ boxBits hell R) :
    rewiredStageAssignment hgood hinternal y R hR i = 0 := by
  have hnode : Encoding.nodeOfBit (2 * ell) i ∈
      ActiveEdge.embeddedSubgrid hell R := mem_boxBits_iff.mp hi
  obtain ⟨u, hu⟩ := ActiveEdge.mem_embeddedSubgrid_iff.mp hnode
  have hsuccessor :
      (rewiredStageInput hgood hinternal y R hR).successor
          (Encoding.nodeOfBit (2 * ell) i) = none := by
    rw [← hu]
    exact rewiredStageInput_nullOn_candidate hgood hinternal y R hR u
  rw [rewiredStageAssignment, Encoding.encodeInput]
  change BinaryPointer.encode
      ((rewiredStageInput hgood hinternal y R hR).successor
        (Encoding.nodeOfBit (2 * ell) i)) _ = 0
  rw [hsuccessor, BinaryPointer.encode_none]
  rfl

theorem encodedPathFamily_distinguished_active
    {hell : 0 < ell}
    {y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2}
    (hy : SoPL.IsEncodedPathFamily ell hell y) :
    (SoPL.Encoding.decodeInput ell y).Active
      (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
  obtain ⟨W⟩ := hy
  obtain ⟨p, hp, hsource⟩ := W.distinguished
  exact (W.active_iff_on_path
    (GridNode.distinguished (BinaryPointer.order_pos hell))).mpr
      ⟨p, hp, hsource⟩

/-- On a path-family stage, the only proper-sink witnesses are active local
last-row sources routed to the parking exit. -/
theorem stageInput_properSinkWitness_iff_mem_activeLastSources
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    {u : GridNode (ActiveEdge.ambientOrder ell)} :
    (stageInput hgood hinternal y).ProperSinkWitness u ↔
      u ∈ activeLastSources hgood hinternal y := by
  let source := SoPL.Encoding.decodeInput ell y
  let ctx := hgood.toStageContext hinternal
  obtain ⟨W⟩ := hy
  have hsourceActive : source.Active
      (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
    exact encodedPathFamily_distinguished_active (hell := hell) ⟨W⟩
  constructor
  · intro hsink
    by_cases hu : u ∈ ActiveEdge.embeddedSubgrid hell s.currentBox
    · obtain ⟨v, hv⟩ := ActiveEdge.mem_embeddedSubgrid_iff.mp hu
      subst u
      rcases v.internal_or_last with hinternalLocal | hlast
      · have hmapped :
            ∃ w, source.ActiveEdge v w ∧ source.ProperSink w :=
          (ActiveEdge.internal_solution_maps_to_properSink
            ctx source v hinternalLocal).mp (by
              simpa [stageInput, ctx, source] using hsink)
        obtain ⟨w, _hedge, hsinkSource⟩ := hmapped
        exact (SoPL.pathFamily_no_internal_sink W w hsinkSource).elim
      · have hactive : source.Active v :=
          (ActiveEdge.last_row_solution_maps_to_activeLast
            ctx source v hlast).mp (by
              simpa [stageInput, ctx, source] using hsink)
        exact mem_activeLastSources_iff.mpr
          ⟨v, hlast, by simpa [source] using hactive, rfl⟩
    · have hnotSource : ¬source.Active
          (GridNode.distinguished (BinaryPointer.order_pos hell)) :=
        ActiveEdge.no_outside_solution ctx source hu (by
          simpa [stageInput, ctx, source] using hsink)
      exact (hnotSource hsourceActive).elim
  · intro hsource
    obtain ⟨v, hlast, hactive, rfl⟩ := mem_activeLastSources_iff.mp hsource
    exact (by
      simpa [stageInput, ctx, source] using
        (ActiveEdge.last_row_solution_maps_to_activeLast
          ctx source v hlast).mpr hactive)

/-- After rewiring, the same active local last-row sources are exactly the
proper-sink witnesses, now targeting the selected candidate corner. -/
theorem rewiredStageInput_properSinkWitness_iff_mem_activeLastSources
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    {u : GridNode (ActiveEdge.ambientOrder ell)} :
    (rewiredStageInput hgood hinternal y R hR).ProperSinkWitness u ↔
      u ∈ activeLastSources hgood hinternal y := by
  let rw := stageRewireSpec hgood hinternal y R hR
  constructor
  · intro hsink
    by_cases hsource : u ∈ activeLastSources hgood hinternal y
    · exact hsource
    · have hsinkAfter : rw.after.ProperSinkWitness u := by
        simpa [rw, stageRewireSpec, RewireSpec.after, rewiredStageInput] using hsink
      have hsinkBefore : rw.before.ProperSinkWitness u :=
        (rw.after_properSinkWitness_iff_before_of_not_mem hsource).mp hsinkAfter
      have hsinkStage : (stageInput hgood hinternal y).ProperSinkWitness u := by
        simpa [rw, stageRewireSpec] using hsinkBefore
      exact (stageInput_properSinkWitness_iff_mem_activeLastSources
        hgood hinternal y hy).mp hsinkStage
  · intro hsource
    have hpoints : rw.after.PointsTo u rw.newExit :=
      ⟨(rw.source_new_designated u hsource).source_nextRow_target,
        rw.source_points_new hsource⟩
    have hinactive : ¬rw.after.Active rw.newExit := by
      intro hactive
      exact hactive rw.after_newExit_null
    have hsink : rw.after.ProperSinkWitness u := ⟨rw.newExit, hpoints, hinactive⟩
    simpa [rw, stageRewireSpec, RewireSpec.after, rewiredStageInput] using hsink

theorem rewiredStageInput_no_inactiveSource
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    ¬SoD.Valid (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
      (rewiredStageInput hgood hinternal y R hR) .inactiveSource := by
  intro hvalid
  let rw := stageRewireSpec hgood hinternal y R hR
  let ambientSource :=
    GridNode.distinguished
      (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
  have hafterInactive : ¬rw.after.Active ambientSource := by
    simpa [SoD.Valid, ambientSource, rw, stageRewireSpec, RewireSpec.after,
      rewiredStageInput] using hvalid
  have hbeforeInactive : ¬rw.before.Active ambientSource := by
    intro hactive
    exact hafterInactive ((rw.after_active_iff_before ambientSource).2 hactive)
  have hstageInactive : ¬(stageInput hgood hinternal y).Active ambientSource := by
    simpa [rw, stageRewireSpec] using hbeforeInactive
  have hlocalInactive :
      ¬(SoPL.Encoding.decodeInput ell y).Active
        (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
    apply ActiveEdge.inactiveSource_maps_to_inactiveSource
      (hgood.toStageContext hinternal) (SoPL.Encoding.decodeInput ell y)
    simpa [stageInput, ambientSource] using hstageInactive
  exact hlocalInactive (encodedPathFamily_distinguished_active (hell := hell) hy)

theorem rewiredStageInput_no_activeLast
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    (u : GridNode (ActiveEdge.ambientOrder ell)) :
    ¬SoD.Valid (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
      (rewiredStageInput hgood hinternal y R hR) (.activeLast u) := by
  rintro ⟨hlast, hactive⟩
  let rw := stageRewireSpec hgood hinternal y R hR
  have hafterActive : rw.after.Active u := by
    simpa [rw, stageRewireSpec, RewireSpec.after, rewiredStageInput] using hactive
  have hbeforeActive : rw.before.Active u :=
    (rw.after_active_iff_before u).mp hafterActive
  apply ActiveEdge.no_activeLast_solution
    (hgood.toStageContext hinternal) (SoPL.Encoding.decodeInput ell y) u
  exact ⟨hlast, by simpa [rw, stageRewireSpec, stageInput] using hbeforeActive⟩

theorem rewiredStageInput_properSink_source_outside_candidate
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    {u : GridNode (ActiveEdge.ambientOrder ell)}
    (hsink : (rewiredStageInput hgood hinternal y R hR).ProperSinkWitness u) :
    u ∉ ActiveEdge.embeddedSubgrid hell R := by
  have hsource : u ∈ activeLastSources hgood hinternal y :=
    (rewiredStageInput_properSinkWitness_iff_mem_activeLastSources
      hgood hinternal y hy R hR).mp hsink
  have hcurrent := activeLastSource_mem_currentSubgrid hsource
  have hne : s.currentBox ≠ R :=
    GridNode.nextRow_ne (SoD.nextCandidate_nextRow hR)
  intro hnew
  exact (Finset.disjoint_left.mp (ActiveEdge.embeddedSubgrid_disjoint hne))
    hcurrent hnew

theorem rewiredStageInput_properSink_pointsTo_candidateCorner
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    {u : GridNode (ActiveEdge.ambientOrder ell)}
    (hsink : (rewiredStageInput hgood hinternal y R hR).ProperSinkWitness u) :
    (rewiredStageInput hgood hinternal y R hR).PointsTo u
      (ActiveEdge.embeddedCorner hell R) := by
  have hsource : u ∈ activeLastSources hgood hinternal y :=
    (rewiredStageInput_properSinkWitness_iff_mem_activeLastSources
      hgood hinternal y hy R hR).mp hsink
  let rw := stageRewireSpec hgood hinternal y R hR
  have hpoints : rw.after.PointsTo u rw.newExit :=
    ⟨(rw.source_new_designated u hsource).source_nextRow_target,
      rw.source_points_new hsource⟩
  simpa [rw, stageRewireSpec, RewireSpec.after, rewiredStageInput] using hpoints

theorem rewiredStageInput_solution_control
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    ∀ o, SoD.Valid (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
        (rewiredStageInput hgood hinternal y R hR) o →
      match o with
      | .inactiveSource =>
          ActiveEdge.embeddedCorner hell R =
            GridNode.distinguished
              (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
      | .activeLast _ => False
      | .properSink u =>
          u ∉ ActiveEdge.embeddedSubgrid hell R ∧
            (rewiredStageInput hgood hinternal y R hR).PointsTo u
              (ActiveEdge.embeddedCorner hell R) := by
  intro o hvalid
  cases o with
  | inactiveSource =>
      exact (rewiredStageInput_no_inactiveSource
        hgood hinternal y hy R hR hvalid).elim
  | activeLast u =>
      exact rewiredStageInput_no_activeLast hgood hinternal y R hR u hvalid
  | properSink u =>
      exact ⟨rewiredStageInput_properSink_source_outside_candidate
          hgood hinternal y hy R hR hvalid,
        rewiredStageInput_properSink_pointsTo_candidateCorner
          hgood hinternal y hy R hR hvalid⟩

/-- Keep the rewired assignment outside `R` and free exactly the bits of `R`. -/
noncomputable def nextRestriction
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    Restriction ell :=
  Restriction.fromAssignmentOutside (boxBits hell R)
    (rewiredStageAssignment hgood hinternal y R hR)

theorem nextRestriction_freeExactly
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextRestriction hgood hinternal y R hR).FreeExactly (boxBits hell R) := by
  exact Restriction.fromAssignmentOutside_freeExactly _ _

theorem nextRestriction_matches_iff
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (nextRestriction hgood hinternal y R hR).Matches z ↔
      ∀ i, i ∉ boxBits hell R →
        z i = rewiredStageAssignment hgood hinternal y R hR i := by
  exact Restriction.matches_fromAssignmentOutside_iff _ _ _

theorem nextRestriction_nullAssignment_eq_rewiredStageAssignment
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextRestriction hgood hinternal y R hR).nullAssignment =
      rewiredStageAssignment hgood hinternal y R hR := by
  apply Restriction.nullAssignment_fromAssignmentOutside_eq
  intro i hi
  exact rewiredStageAssignment_eq_zero_of_mem_boxBits
    hgood hinternal y R hR hi

theorem nextRestriction_nullInput_eq_rewiredStageInput
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextRestriction hgood hinternal y R hR).nullInput =
      rewiredStageInput hgood hinternal y R hR := by
  rw [Restriction.nullInput,
    nextRestriction_nullAssignment_eq_rewiredStageAssignment]
  exact Encoding.decodeInput_encodeInput _

/-- The next mutable state has the selected box, the next stage, and exact
`7 / 5` bound. -/
noncomputable def nextState
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    AmpState ell where
  stage := s.stage + 1
  restriction := nextRestriction hgood hinternal y R hR
  currentBox := R
  B := (7 / 5 : ℝ) * s.B

@[simp]
theorem nextState_stage
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextState hgood hinternal y R hR).stage = s.stage + 1 := rfl

@[simp]
theorem nextState_restriction
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextState hgood hinternal y R hR).restriction =
      nextRestriction hgood hinternal y R hR := rfl

@[simp]
theorem nextState_currentBox
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextState hgood hinternal y R hR).currentBox = R := rfl

@[simp]
theorem nextState_B
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextState hgood hinternal y R hR).B = (7 / 5 : ℝ) * s.B := rfl

@[simp]
theorem nextState_nullInput_eq_rewiredStageInput
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    (nextState hgood hinternal y R hR).nullInput =
      rewiredStageInput hgood hinternal y R hR := by
  exact nextRestriction_nullInput_eq_rewiredStageInput
    hgood hinternal y R hR

theorem nextState_structural
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox) :
    StructuralInvariant hell (nextState hgood hinternal y R hR) := by
  constructor
  · exact nextRestriction_freeExactly hgood hinternal y R hR
  · intro S hrow
    rw [nextState_nullInput_eq_rewiredStageInput]
    exact rewiredStageInput_nullAfter_candidate
      hgood hinternal y R hR S hrow
  · intro o hvalid
    have hvalid' : SoD.Valid
        (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
        (rewiredStageInput hgood hinternal y R hR) o := by
      simpa using hvalid
    cases o with
    | inactiveSource =>
        exact (rewiredStageInput_no_inactiveSource
          hgood hinternal y hy R hR hvalid').elim
    | activeLast u =>
        exact rewiredStageInput_no_activeLast
          hgood hinternal y R hR u hvalid'
    | properSink u =>
        rw [nextState_nullInput_eq_rewiredStageInput]
        exact ⟨rewiredStageInput_properSink_source_outside_candidate
            hgood hinternal y hy R hR hvalid',
          rewiredStageInput_properSink_pointsTo_candidateCorner
            hgood hinternal y hy R hR hvalid'⟩

theorem good_nextState
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hy : SoPL.IsEncodedPathFamily ell hell y)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    (hnumerical :
      ∀ z, (∀ i, i ∉ boxBits hell R →
        z i = rewiredStageAssignment hgood hinternal y R hR i) →
        (7 / 5 : ℝ) * s.B ≤ 1 + JR.eval z) :
    GoodState hell JR (nextState hgood hinternal y R hR) := by
  have hnext := SoD.nextCandidate_nextRow hR
  have hrow : R.row.val = s.stage + 1 := by
    unfold GridNode.NextRow at hnext
    rw [hgood.row_eq_stage] at hnext
    exact hnext
  constructor
  · rw [nextState_stage, ← hrow]
    exact R.row.isLt
  · rw [nextState_currentBox, nextState_stage]
    exact hrow
  · rw [nextState_currentBox]
    exact (SoD.mem_nextMacroRowCandidates_iff.mp hR).2
  · rw [nextState_B]
    nlinarith [hgood.one_le_B]
  · exact nextState_structural hgood hinternal y hy R hR
  · intro z hmatch
    rw [nextState_B]
    apply hnumerical z
    apply (nextRestriction_matches_iff hgood hinternal y R hR z).mp
    simpa using hmatch

end Amplification

end SoD

end Revres
