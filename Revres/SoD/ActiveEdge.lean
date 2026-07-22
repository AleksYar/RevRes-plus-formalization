import Revres.DecisionTree.ClauseSearch
import Revres.DecisionTree.Transfer
import Revres.SoD.Encoding
import Revres.SoD.MacroGrid
import Revres.SoPL.Encoding

/-!
# Active-edge formulation

An exact binary SoPL instance of order `2 ^ ell - 1` is embedded in one box of a checked
`n * n` macrogrid core.  The core sits inside the exact binary SoD order `2 ^ (2 * ell) - 1`.
-/

namespace Revres

open Lemma53

namespace SoD

namespace ActiveEdge

abbrev localOrder (ell : ℕ) : ℕ := BinaryPointer.order ell

abbrev ambientOrder (ell : ℕ) : ℕ := BinaryPointer.order (2 * ell)

theorem ambientWidth_pos {ell : ℕ} (hell : 0 < ell) : 0 < 2 * ell :=
  Nat.mul_pos (by decide) hell

theorem ambientOrder_eq (ell : ℕ) :
    ambientOrder ell = localOrder ell * (localOrder ell + 2) := by
  let q := 2 ^ ell
  have hq : 1 ≤ q := by
    exact one_le_pow₀ (by decide)
  have hpow : 2 ^ (2 * ell) = q * q := by
    rw [show 2 * ell = ell + ell by omega, pow_add]
  change 2 ^ (2 * ell) - 1 = (2 ^ ell - 1) * (2 ^ ell - 1 + 2)
  rw [hpow]
  change q * q - 1 = (q - 1) * (q - 1 + 2)
  have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq
  let n := q - 1
  have hqn : q = n + 1 := hsub.symm
  rw [hqn]
  change (n + 1) * (n + 1) - 1 = n * (n + 2)
  calc
    (n + 1) * (n + 1) - 1 = (n * n + 2 * n + 1) - 1 := by ring_nf
    _ = n * n + 2 * n := by omega
    _ = n * (n + 2) := by ring

theorem coreOrder_lt_ambientOrder {ell : ℕ} (hell : 0 < ell) :
    localOrder ell * localOrder ell < ambientOrder ell := by
  rw [ambientOrder_eq]
  have hn : 0 < localOrder ell := BinaryPointer.order_pos hell
  nlinarith

theorem coreOrder_le_ambientOrder {ell : ℕ} (hell : 0 < ell) :
    localOrder ell * localOrder ell ≤ ambientOrder ell :=
  Nat.le_of_lt (coreOrder_lt_ambientOrder hell)

/-- Checked inclusion of the manuscript's `n * n` grid into the exact binary ambient order. -/
def coreEmbed {ell : ℕ} (hell : 0 < ell) :
    GridNode (localOrder ell * localOrder ell) → GridNode (ambientOrder ell) := fun v =>
  (Fin.castLE (coreOrder_le_ambientOrder hell) v.row,
    Fin.castLE (coreOrder_le_ambientOrder hell) v.column)

@[simp] theorem coreEmbed_row_val {ell : ℕ} (hell : 0 < ell)
    (v : GridNode (localOrder ell * localOrder ell)) :
    (coreEmbed hell v).row.val = v.row.val :=
  rfl

@[simp] theorem coreEmbed_column_val {ell : ℕ} (hell : 0 < ell)
    (v : GridNode (localOrder ell * localOrder ell)) :
    (coreEmbed hell v).column.val = v.column.val :=
  rfl

theorem coreEmbed_injective {ell : ℕ} (hell : 0 < ell) :
    Function.Injective (coreEmbed hell) := by
  intro u v huv
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun w => w.row.val) huv
  · exact congrArg (fun w => w.column.val) huv

/-- Embed a local node in macro-box `Q` into the padded ambient grid. -/
def embedNode {ell : ℕ} (hell : 0 < ell)
    (Q u : GridNode (localOrder ell)) : GridNode (ambientOrder ell) :=
  coreEmbed hell (SoD.macroEmbed Q u)

theorem embedNode_right_injective {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) : Function.Injective (embedNode hell Q) := by
  intro u v huv
  exact SoD.macroEmbed_right_injective Q (coreEmbed_injective hell huv)

/-- The image of one local macro-box in the padded ambient grid. -/
def embeddedSubgrid {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) : Finset (GridNode (ambientOrder ell)) :=
  Finset.univ.image (embedNode hell Q)

theorem mem_embeddedSubgrid_iff {ell : ℕ} {hell : 0 < ell}
    {Q : GridNode (localOrder ell)} {v : GridNode (ambientOrder ell)} :
    v ∈ embeddedSubgrid hell Q ↔ ∃ u, embedNode hell Q u = v := by
  simp [embeddedSubgrid]

theorem embeddedSubgrid_disjoint {ell : ℕ} {hell : 0 < ell}
    {Q R : GridNode (localOrder ell)} (hQR : Q ≠ R) :
    Disjoint (embeddedSubgrid hell Q) (embeddedSubgrid hell R) := by
  rw [Finset.disjoint_left]
  intro v hvQ hvR
  obtain ⟨u, hu⟩ := mem_embeddedSubgrid_iff.mp hvQ
  obtain ⟨w, hw⟩ := mem_embeddedSubgrid_iff.mp hvR
  have hcore : SoD.macroEmbed Q u = SoD.macroEmbed R w :=
    coreEmbed_injective hell (hu.trans hw.symm)
  have hindex := congrArg SoD.macroIndex hcore
  exact hQR (by simpa using hindex)

/-- The unique local node represented by an ambient node known to lie in a box. -/
noncomputable def localOfMem {ell : ℕ} {hell : 0 < ell}
    {Q : GridNode (localOrder ell)} (v : GridNode (ambientOrder ell))
    (hv : v ∈ embeddedSubgrid hell Q) : GridNode (localOrder ell) :=
  Classical.choose (mem_embeddedSubgrid_iff.mp hv)

@[simp] theorem embedNode_localOfMem {ell : ℕ} {hell : 0 < ell}
    {Q : GridNode (localOrder ell)} (v : GridNode (ambientOrder ell))
    (hv : v ∈ embeddedSubgrid hell Q) :
    embedNode hell Q (localOfMem v hv) = v :=
  Classical.choose_spec (mem_embeddedSubgrid_iff.mp hv)

/-- Partial inverse for the local-node embedding. -/
noncomputable def embeddedLocalNode {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) (v : GridNode (ambientOrder ell)) :
    Option (GridNode (localOrder ell)) :=
  if hv : v ∈ embeddedSubgrid hell Q then some (localOfMem v hv) else none

theorem embeddedLocalNode_eq_some_iff {ell : ℕ} {hell : 0 < ell}
    {Q : GridNode (localOrder ell)} {v : GridNode (ambientOrder ell)}
    {u : GridNode (localOrder ell)} :
    embeddedLocalNode hell Q v = some u ↔ embedNode hell Q u = v := by
  by_cases hv : v ∈ embeddedSubgrid hell Q
  · rw [embeddedLocalNode, dif_pos hv, Option.some.injEq]
    constructor
    · rintro rfl
      exact embedNode_localOfMem v hv
    · intro hu
      exact embedNode_right_injective hell Q
        ((embedNode_localOfMem v hv).trans hu.symm)
  · rw [embeddedLocalNode, dif_neg hv]
    simp only [reduceCtorEq, false_iff]
    intro hu
    exact hv (mem_embeddedSubgrid_iff.mpr ⟨u, hu⟩)

/-- Top-left corner of an embedded macro-box. -/
def embeddedCorner {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) : GridNode (ambientOrder ell) :=
  embedNode hell Q (GridNode.distinguished (BinaryPointer.order_pos hell))

theorem embeddedCorner_mem {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) :
    embeddedCorner hell Q ∈ embeddedSubgrid hell Q :=
  mem_embeddedSubgrid_iff.mpr
    ⟨GridNode.distinguished (BinaryPointer.order_pos hell), rfl⟩

theorem distinguished_embeddedCorner {ell : ℕ} (hell : 0 < ell) :
    embeddedCorner hell (GridNode.distinguished (BinaryPointer.order_pos hell)) =
      GridNode.distinguished (BinaryPointer.order_pos (ambientWidth_pos hell)) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [embeddedCorner, embedNode, coreEmbed, SoD.macroEmbed, GridNode.distinguished,
      finProdFinEquiv]

theorem embedNode_nextRow {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) {u v : GridNode (localOrder ell)}
    (huv : u.NextRow v) : (embedNode hell Q u).NextRow (embedNode hell Q v) := by
  unfold GridNode.NextRow at *
  change v.1.val = u.1.val + 1 at huv
  change (SoD.macroEmbed Q v).row.val = (SoD.macroEmbed Q u).row.val + 1
  simp [SoD.macroEmbed, finProdFinEquiv]
  omega

theorem embedded_lastRow_nextRow_corner {ell : ℕ} (hell : 0 < ell)
    {Q R : GridNode (localOrder ell)} (hQR : Q.NextRow R)
    {u : GridNode (localOrder ell)} (hu : u.IsLastRow) :
    (embedNode hell Q u).NextRow (embeddedCorner hell R) := by
  unfold GridNode.NextRow GridNode.IsLastRow at *
  change R.row.val = Q.row.val + 1 at hQR
  change u.row.val + 1 = localOrder ell at hu
  change (SoD.macroEmbed R (GridNode.distinguished
    (BinaryPointer.order_pos hell))).row.val = (SoD.macroEmbed Q u).row.val + 1
  have hleft :
      (SoD.macroEmbed R (GridNode.distinguished
        (BinaryPointer.order_pos hell))).row.val = localOrder ell * R.row.val := by
    simp [SoD.macroEmbed, finProdFinEquiv, GridNode.distinguished]
  have hright :
      (SoD.macroEmbed Q u).row.val = u.row.val + localOrder ell * Q.row.val := by
    simp [SoD.macroEmbed, finProdFinEquiv]
  rw [hleft, hright, hQR]
  nlinarith

/-- Fixed outside data and the exact solution invariant required for one active-edge stage. -/
structure StageContext (ell : ℕ) (hell : 0 < ell) where
  currentBox : GridNode (localOrder ell)
  current_internal : currentBox.IsInternal
  current_candidate :
    currentBox.column ≠ SoD.parkingColumn (BinaryPointer.order_pos hell)
  exitBox : GridNode (localOrder ell)
  exit_nextRow : currentBox.NextRow exitBox
  base : SoD.Input (ambientOrder ell)
  base_null_current :
    ∀ u, base.successor (embedNode hell currentBox u) = none
  exit_inactive : ¬base.Active (embeddedCorner hell exitBox)
  base_solution_control :
    ∀ o, SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell)) base o →
      match o with
      | .inactiveSource =>
          embeddedCorner hell currentBox =
            GridNode.distinguished (BinaryPointer.order_pos (ambientWidth_pos hell))
      | .activeLast _ => False
      | .properSink u =>
          u ∉ embeddedSubgrid hell currentBox ∧
            base.PointsTo u (embeddedCorner hell currentBox)

namespace StageContext

variable {ell : ℕ} {hell : 0 < ell}

theorem current_ne_exit (ctx : StageContext ell hell) :
    ctx.currentBox ≠ ctx.exitBox :=
  GridNode.nextRow_ne ctx.exit_nextRow

theorem exit_not_mem_current (ctx : StageContext ell hell) :
    embeddedCorner hell ctx.exitBox ∉ embeddedSubgrid hell ctx.currentBox := by
  intro hmem
  have hdisjoint :
      Disjoint (embeddedSubgrid hell ctx.currentBox) (embeddedSubgrid hell ctx.exitBox) :=
    embeddedSubgrid_disjoint ctx.current_ne_exit
  exact (Finset.disjoint_left.mp hdisjoint) hmem
    (embeddedCorner_mem hell ctx.exitBox)

end StageContext

@[simp] theorem embeddedLocalNode_embedNode {ell : ℕ} {hell : 0 < ell}
    (Q : GridNode (localOrder ell)) (u : GridNode (localOrder ell)) :
    embeddedLocalNode hell Q (embedNode hell Q u) = some u :=
  embeddedLocalNode_eq_some_iff.mpr rfl

theorem embeddedLocalNode_eq_none_of_not_mem {ell : ℕ} {hell : 0 < ell}
    {Q : GridNode (localOrder ell)} {v : GridNode (ambientOrder ell)}
    (hv : v ∉ embeddedSubgrid hell Q) :
    embeddedLocalNode hell Q v = none := by
  simp [embeddedLocalNode, hv]

theorem embeddedLocalNode_eq_none_iff {ell : ℕ} {hell : 0 < ell}
    {Q : GridNode (localOrder ell)} {v : GridNode (ambientOrder ell)} :
    embeddedLocalNode hell Q v = none ↔ v ∉ embeddedSubgrid hell Q := by
  constructor
  · intro hnone hmem
    obtain ⟨u, rfl⟩ := mem_embeddedSubgrid_iff.mp hmem
    simp at hnone
  · exact embeddedLocalNode_eq_none_of_not_mem

/-- Embed mutual SoPL edges in the current box and route active local sinks to the exit. -/
noncomputable def activeEdgeEmbedding {ell : ℕ} {hell : 0 < ell}
    (ctx : StageContext ell hell) (y : SoPL.Input (localOrder ell)) :
    SoD.Input (ambientOrder ell) where
  successor v :=
    match embeddedLocalNode hell ctx.currentBox v with
    | none => ctx.base.successor v
    | some u =>
        if _ : u.IsInternal then
          match y.nextNode u with
          | none => none
          | some w => some (embedNode hell ctx.currentBox w).column
        else if y.Active u then
          some (embeddedCorner hell ctx.exitBox).column
        else none

theorem activeEdgeEmbedding_outside {ell : ℕ} {hell : 0 < ell}
    (ctx : StageContext ell hell) (y : SoPL.Input (localOrder ell))
    {v : GridNode (ambientOrder ell)} (hv : v ∉ embeddedSubgrid hell ctx.currentBox) :
    (activeEdgeEmbedding ctx y).successor v = ctx.base.successor v := by
  simp [activeEdgeEmbedding, embeddedLocalNode_eq_none_of_not_mem hv]

theorem activeEdgeEmbedding_internal_successor {ell : ℕ} {hell : 0 < ell}
    (ctx : StageContext ell hell) (y : SoPL.Input (localOrder ell))
    (u : GridNode (localOrder ell)) (hu : u.IsInternal) :
    (activeEdgeEmbedding ctx y).successor (embedNode hell ctx.currentBox u) =
      (y.nextNode u).map fun v => (embedNode hell ctx.currentBox v).column := by
  simp only [activeEdgeEmbedding, embeddedLocalNode_embedNode, hu, dif_pos]
  cases y.nextNode u <;> rfl

theorem activeEdgeEmbedding_last_successor {ell : ℕ} {hell : 0 < ell}
    (ctx : StageContext ell hell) (y : SoPL.Input (localOrder ell))
    (u : GridNode (localOrder ell)) (hu : u.IsLastRow) :
    (activeEdgeEmbedding ctx y).successor (embedNode hell ctx.currentBox u) =
      if y.Active u then some (embeddedCorner hell ctx.exitBox).column else none := by
  have hnot : ¬u.IsInternal := GridNode.not_internal_of_last hu
  simp [activeEdgeEmbedding, hnot]

theorem embedNode_nextRow_iff {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) {u v : GridNode (localOrder ell)} :
    (embedNode hell Q u).NextRow (embedNode hell Q v) ↔ u.NextRow v := by
  constructor
  · intro h
    unfold GridNode.NextRow at h ⊢
    change (SoD.macroEmbed Q v).row.val = (SoD.macroEmbed Q u).row.val + 1 at h
    simp [SoD.macroEmbed, finProdFinEquiv] at h
    change v.1.val = u.1.val + 1
    omega
  · exact embedNode_nextRow hell Q

theorem embedNode_column_injective {ell : ℕ} (hell : 0 < ell)
    (Q : GridNode (localOrder ell)) {u v : GridNode (localOrder ell)}
    (h : (embedNode hell Q u).column = (embedNode hell Q v).column) :
    u.column = v.column := by
  apply Fin.ext
  have hval := congrArg Fin.val h
  change (SoD.macroEmbed Q u).column.val = (SoD.macroEmbed Q v).column.val at hval
  simp [SoD.macroEmbed, finProdFinEquiv] at hval
  change u.2.val = v.2.val
  omega

theorem activeEdgeEmbedding_internal_pointsTo_iff
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u v : GridNode (localOrder ell))
    (hu : u.IsInternal) :
    (activeEdgeEmbedding ctx y).PointsTo
        (embedNode hell ctx.currentBox u) (embedNode hell ctx.currentBox v) ↔
      y.ActiveEdge u v := by
  rw [SoD.Input.PointsTo, ← y.nextNode_eq_some_iff u v]
  constructor
  · rintro ⟨hrow, hsucc⟩
    have hlocalRow : u.NextRow v :=
      (embedNode_nextRow_iff hell ctx.currentBox).mp hrow
    rw [activeEdgeEmbedding_internal_successor ctx y u hu] at hsucc
    cases hnext : y.nextNode u with
    | none => simp [hnext] at hsucc
    | some w =>
        simp only [hnext, Option.map_some, Option.some.injEq] at hsucc
        have hwrow : u.NextRow w :=
          (y.nextNode_eq_some_iff u w).mp hnext |>.1
        have hcol : w.column = v.column :=
          embedNode_column_injective hell ctx.currentBox hsucc
        apply congrArg some
        apply Prod.ext
        · exact GridNode.nextRow_row_unique hwrow hlocalRow
        · exact hcol
  · intro hnext
    have hedge := (y.nextNode_eq_some_iff u v).mp hnext
    constructor
    · exact embedNode_nextRow hell ctx.currentBox hedge.1
    · simp [activeEdgeEmbedding_internal_successor ctx y u hu, hnext]

theorem activeEdgeEmbedding_internal_active_iff
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u : GridNode (localOrder ell))
    (hu : u.IsInternal) :
    (activeEdgeEmbedding ctx y).Active (embedNode hell ctx.currentBox u) ↔
      y.Active u := by
  rw [SoD.Input.Active, activeEdgeEmbedding_internal_successor ctx y u hu]
  rw [y.active_internal_iff hu]
  constructor
  · intro h
    cases hnext : y.nextNode u with
    | none => exact (h (by simp [hnext])).elim
    | some v => exact ⟨v, (y.nextNode_eq_some_iff u v).mp hnext⟩
  · rintro ⟨v, hedge⟩
    rw [← y.nextNode_eq_some_iff] at hedge
    simp [hedge]

theorem activeEdgeEmbedding_last_active_iff
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u : GridNode (localOrder ell))
    (hu : u.IsLastRow) :
    (activeEdgeEmbedding ctx y).Active (embedNode hell ctx.currentBox u) ↔
      y.Active u := by
  rw [SoD.Input.Active, activeEdgeEmbedding_last_successor ctx y u hu]
  by_cases hactive : y.Active u <;> simp [hactive]

theorem activeEdgeEmbedding_active_iff
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u : GridNode (localOrder ell)) :
    (activeEdgeEmbedding ctx y).Active (embedNode hell ctx.currentBox u) ↔
      y.Active u := by
  rcases u.internal_or_last with hu | hu
  · exact activeEdgeEmbedding_internal_active_iff ctx y u hu
  · exact activeEdgeEmbedding_last_active_iff ctx y u hu

theorem activeEdgeEmbedding_last_pointsTo_exit_iff
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u : GridNode (localOrder ell))
    (hu : u.IsLastRow) :
    (activeEdgeEmbedding ctx y).PointsTo
        (embedNode hell ctx.currentBox u) (embeddedCorner hell ctx.exitBox) ↔
      y.Active u := by
  rw [SoD.Input.PointsTo, activeEdgeEmbedding_last_successor ctx y u hu]
  have hrow := embedded_lastRow_nextRow_corner hell ctx.exit_nextRow hu
  by_cases hactive : y.Active u <;> simp [hactive, hrow]

theorem activeEdgeEmbedding_corner_active_iff
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) :
    (activeEdgeEmbedding ctx y).Active (embeddedCorner hell ctx.currentBox) ↔
      y.Active (GridNode.distinguished (BinaryPointer.order_pos hell)) :=
  activeEdgeEmbedding_active_iff ctx y _

theorem activeEdgeEmbedding_exit_inactive
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) :
    ¬(activeEdgeEmbedding ctx y).Active (embeddedCorner hell ctx.exitBox) := by
  rw [SoD.Input.Active, activeEdgeEmbedding_outside ctx y ctx.exit_not_mem_current]
  exact ctx.exit_inactive

theorem old_solution_disappears_when_corner_active
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) {u : GridNode (ambientOrder ell)}
    (hu : u ∉ embeddedSubgrid hell ctx.currentBox)
    (hpoints : ctx.base.PointsTo u (embeddedCorner hell ctx.currentBox)) :
    (activeEdgeEmbedding ctx y).ProperSinkWitness u ↔
      ¬y.Active (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
  have hembed :
      (activeEdgeEmbedding ctx y).PointsTo u (embeddedCorner hell ctx.currentBox) := by
    exact ⟨hpoints.1, by
      rw [activeEdgeEmbedding_outside ctx y hu]
      exact hpoints.2⟩
  constructor
  · rintro ⟨v, huv, hinactive⟩
    have hv : v = embeddedCorner hell ctx.currentBox :=
      (activeEdgeEmbedding ctx y).pointsTo_target_unique huv hembed
    rw [hv] at hinactive
    exact (not_congr (activeEdgeEmbedding_corner_active_iff ctx y)).mp hinactive
  · intro hinactive
    exact ⟨embeddedCorner hell ctx.currentBox, hembed,
      (not_congr (activeEdgeEmbedding_corner_active_iff ctx y)).mpr hinactive⟩

theorem internal_solution_maps_to_properSink
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u : GridNode (localOrder ell))
    (hu : u.IsInternal) :
    (activeEdgeEmbedding ctx y).ProperSinkWitness
        (embedNode hell ctx.currentBox u) ↔
      ∃ v, y.ActiveEdge u v ∧ y.ProperSink v := by
  constructor
  · rintro ⟨z, huz, hzinactive⟩
    have huactive : y.Active u :=
      (activeEdgeEmbedding_internal_active_iff ctx y u hu).mp
        ((activeEdgeEmbedding ctx y).active_internal_iff_exists_pointsTo
          (GridNode.nextRow_internal huz.1) |>.mpr ⟨z, huz⟩)
    obtain ⟨v, hedge⟩ := (y.active_internal_iff hu).mp huactive
    have huv : (activeEdgeEmbedding ctx y).PointsTo
        (embedNode hell ctx.currentBox u) (embedNode hell ctx.currentBox v) :=
      (activeEdgeEmbedding_internal_pointsTo_iff ctx y u v hu).mpr hedge
    have hz : z = embedNode hell ctx.currentBox v :=
      (activeEdgeEmbedding ctx y).pointsTo_target_unique huz huv
    subst z
    have hvinactive : ¬y.Active v :=
      (not_congr (activeEdgeEmbedding_active_iff ctx y v)).mp hzinactive
    exact ⟨v, hedge, hvinactive, ⟨u, hedge⟩⟩
  · rintro ⟨v, hedge, hvinactive, _hincoming⟩
    exact ⟨embedNode hell ctx.currentBox v,
      (activeEdgeEmbedding_internal_pointsTo_iff ctx y u v hu).mpr hedge,
      (not_congr (activeEdgeEmbedding_active_iff ctx y v)).mpr hvinactive⟩

theorem last_row_solution_maps_to_activeLast
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u : GridNode (localOrder ell))
    (hu : u.IsLastRow) :
    (activeEdgeEmbedding ctx y).ProperSinkWitness
        (embedNode hell ctx.currentBox u) ↔
      y.Active u := by
  have hexit : (activeEdgeEmbedding ctx y).PointsTo
      (embedNode hell ctx.currentBox u) (embeddedCorner hell ctx.exitBox) ↔
      y.Active u :=
    activeEdgeEmbedding_last_pointsTo_exit_iff ctx y u hu
  constructor
  · rintro ⟨v, hpoints, _hinactive⟩
    exact (activeEdgeEmbedding_last_active_iff ctx y u hu).mp
      (fun hnone => Option.some_ne_none _ (hpoints.2.symm.trans hnone))
  · intro hactive
    exact ⟨embeddedCorner hell ctx.exitBox, hexit.mpr hactive,
      activeEdgeEmbedding_exit_inactive ctx y⟩

theorem base_inactive_on_current
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (u : GridNode (localOrder ell)) :
    ¬ctx.base.Active (embedNode hell ctx.currentBox u) := by
  simp [SoD.Input.Active, ctx.base_null_current]

theorem activeEdgeEmbedding_active_outside_iff
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) {v : GridNode (ambientOrder ell)}
    (hv : v ∉ embeddedSubgrid hell ctx.currentBox) :
    (activeEdgeEmbedding ctx y).Active v ↔ ctx.base.Active v := by
  simp [SoD.Input.Active, activeEdgeEmbedding_outside ctx y hv]

theorem embedded_node_not_lastRow
    {ell : ℕ} {hell : 0 < ell} (Q : GridNode (localOrder ell))
    (u : GridNode (localOrder ell)) :
    ¬(embedNode hell Q u).IsLastRow := by
  intro hlast
  unfold GridNode.IsLastRow at hlast
  have hcore : (SoD.macroEmbed Q u).row.val < localOrder ell * localOrder ell :=
    (SoD.macroEmbed Q u).row.isLt
  change (SoD.macroEmbed Q u).row.val + 1 = ambientOrder ell at hlast
  have hambient := coreOrder_lt_ambientOrder hell
  omega

theorem corner_eq_distinguished_of_distinguished_mem
    {ell : ℕ} {hell : 0 < ell} (Q : GridNode (localOrder ell))
    (hmem : GridNode.distinguished (BinaryPointer.order_pos (ambientWidth_pos hell)) ∈
      embeddedSubgrid hell Q) :
    embeddedCorner hell Q =
      GridNode.distinguished (BinaryPointer.order_pos (ambientWidth_pos hell)) := by
  obtain ⟨u, hu⟩ := mem_embeddedSubgrid_iff.mp hmem
  let sourceBox := GridNode.distinguished (BinaryPointer.order_pos hell)
  let sourceNode := GridNode.distinguished (BinaryPointer.order_pos hell)
  have hsource : embedNode hell sourceBox sourceNode =
      GridNode.distinguished (BinaryPointer.order_pos (ambientWidth_pos hell)) := by
    simpa [embeddedCorner, sourceBox, sourceNode] using distinguished_embeddedCorner hell
  have hcore : SoD.macroEmbed Q u = SoD.macroEmbed sourceBox sourceNode :=
    coreEmbed_injective hell (hu.trans hsource.symm)
  have hQ : Q = sourceBox := by
    have := congrArg SoD.macroIndex hcore
    simpa using this
  subst Q
  exact distinguished_embeddedCorner hell

theorem inactiveSource_maps_to_inactiveSource
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell))
    (htarget : ¬(activeEdgeEmbedding ctx y).Active
      (GridNode.distinguished (BinaryPointer.order_pos (ambientWidth_pos hell)))) :
    ¬y.Active (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
  let ambientSource :=
    GridNode.distinguished (BinaryPointer.order_pos (ambientWidth_pos hell))
  by_cases hcorner : embeddedCorner hell ctx.currentBox = ambientSource
  · apply (not_congr (activeEdgeEmbedding_corner_active_iff ctx y)).mp
    simpa [ambientSource, hcorner] using htarget
  · have houtside : ambientSource ∉ embeddedSubgrid hell ctx.currentBox := by
      intro hmem
      exact hcorner (corner_eq_distinguished_of_distinguished_mem ctx.currentBox hmem)
    have hbase : ¬ctx.base.Active ambientSource :=
      (not_congr (activeEdgeEmbedding_active_outside_iff ctx y houtside)).mp
        (by simpa [ambientSource] using htarget)
    have hvalid : SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell))
        ctx.base .inactiveSource := by
      simpa [SoD.Valid, ambientSource] using hbase
    exact (hcorner (ctx.base_solution_control .inactiveSource hvalid)).elim

theorem no_outside_solution
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) {u : GridNode (ambientOrder ell)}
    (hu : u ∉ embeddedSubgrid hell ctx.currentBox)
    (htarget : (activeEdgeEmbedding ctx y).ProperSinkWitness u) :
    ¬y.Active (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
  obtain ⟨v, huv, hvinactive⟩ := htarget
  have htarget' : (activeEdgeEmbedding ctx y).ProperSinkWitness u :=
    ⟨v, huv, hvinactive⟩
  have hbasePoints : ctx.base.PointsTo u v := by
    refine ⟨huv.1, ?_⟩
    rw [← activeEdgeEmbedding_outside ctx y hu]
    exact huv.2
  have hbaseInactive : ¬ctx.base.Active v := by
    by_cases hv : v ∈ embeddedSubgrid hell ctx.currentBox
    · obtain ⟨w, hw⟩ := mem_embeddedSubgrid_iff.mp hv
      subst v
      exact base_inactive_on_current ctx w
    · intro hactive
      exact hvinactive ((activeEdgeEmbedding_active_outside_iff ctx y hv).mpr hactive)
  have hbaseValid : SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell))
      ctx.base (.properSink u) :=
    ⟨v, hbasePoints, hbaseInactive⟩
  obtain ⟨hu', hcorner⟩ := ctx.base_solution_control (.properSink u) hbaseValid
  exact (old_solution_disappears_when_corner_active ctx y hu' hcorner).mp htarget'

theorem no_activeLast_solution
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : SoPL.Input (localOrder ell)) (u : GridNode (ambientOrder ell)) :
    ¬SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell))
      (activeEdgeEmbedding ctx y) (.activeLast u) := by
  rintro ⟨hlast, hactive⟩
  by_cases hu : u ∈ embeddedSubgrid hell ctx.currentBox
  · obtain ⟨v, hv⟩ := mem_embeddedSubgrid_iff.mp hu
    subst u
    exact embedded_node_not_lastRow ctx.currentBox v hlast
  · have hbaseActive : ctx.base.Active u :=
      (activeEdgeEmbedding_active_outside_iff ctx y hu).mp hactive
    have hbaseValid : SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell))
        ctx.base (.activeLast u) := ⟨hlast, hbaseActive⟩
    exact ctx.base_solution_control (.activeLast u) hbaseValid

private noncomputable def embeddedInternalSuccessorTree
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (u : GridNode (localOrder ell)) (hu : u.IsInternal) :
    DecisionTree (SoPL.Encoding.variableCount ell) (Option (Fin (ambientOrder ell))) :=
  (SoPL.Encoding.readSuccessor ell u).bind fun successor =>
    match successor with
    | none => .leaf none
    | some column =>
        let w := u.next hu column
        (SoPL.Encoding.readPredecessor ell w).map fun predecessor =>
          if predecessor = some u.column then
            some (embedNode hell ctx.currentBox w).column
          else
            none

private theorem embeddedInternalSuccessorTree_depth
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (u : GridNode (localOrder ell)) (hu : u.IsInternal) :
    (embeddedInternalSuccessorTree ctx u hu).depth ≤ 2 * ell := by
  unfold embeddedInternalSuccessorTree
  apply (DecisionTree.depth_bind_le _ _ (d := ell) ?_).trans
  · simp [two_mul]
  · intro successor
    cases successor <;> simp

/-- The target successor stored at one ambient node, computed from the source bits. -/
noncomputable def embeddedSuccessorTree
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (v : GridNode (ambientOrder ell)) :
    DecisionTree (SoPL.Encoding.variableCount ell) (Option (Fin (ambientOrder ell))) :=
  match embeddedLocalNode hell ctx.currentBox v with
  | none => .leaf (ctx.base.successor v)
  | some u =>
      if hu : u.IsInternal then
        embeddedInternalSuccessorTree ctx u hu
      else
        (SoPL.Encoding.readSuccessor ell u).map fun successor =>
          if successor ≠ none then
            some (embeddedCorner hell ctx.exitBox).column
          else
            none

@[simp]
theorem eval_embeddedSuccessorTree
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (v : GridNode (ambientOrder ell))
    (y : Fin (SoPL.Encoding.variableCount ell) → F2) :
    (embeddedSuccessorTree ctx v).eval y =
      (activeEdgeEmbedding ctx (SoPL.Encoding.decodeInput ell y)).successor v := by
  cases hlocal : embeddedLocalNode hell ctx.currentBox v with
  | none =>
      simp [embeddedSuccessorTree, activeEdgeEmbedding, hlocal]
  | some u =>
      have hv : v = embedNode hell ctx.currentBox u :=
        (embeddedLocalNode_eq_some_iff.mp hlocal).symm
      subst v
      let source := SoPL.Encoding.decodeInput ell y
      by_cases hu : u.IsInternal
      · rw [activeEdgeEmbedding_internal_successor ctx source u hu]
        simp only [embeddedSuccessorTree, embeddedLocalNode_embedNode, hu, dif_pos,
          embeddedInternalSuccessorTree, DecisionTree.eval_bind,
          SoPL.Encoding.eval_readSuccessor]
        change (match source.successor u with
          | none => DecisionTree.leaf none
          | some column =>
              let w := u.next hu column
              (SoPL.Encoding.readPredecessor ell w).map fun predecessor =>
                if predecessor = some u.column then
                  some (embedNode hell ctx.currentBox w).column
                else none).eval y =
            (source.nextNode u).map fun w =>
              (embedNode hell ctx.currentBox w).column
        cases hs : source.successor u with
        | none =>
            simp [SoPL.Input.nextNode, hu, hs]
        | some column =>
            rw [DecisionTree.eval_map, SoPL.Encoding.eval_readPredecessor]
            change (if source.predecessor (u.next hu column) = some u.column then
                some (embedNode hell ctx.currentBox (u.next hu column)).column else none) =
              (source.nextNode u).map fun w =>
                (embedNode hell ctx.currentBox w).column
            simp [SoPL.Input.nextNode, hu, hs]
      · have hlast : u.IsLastRow := u.internal_or_last.resolve_left hu
        rw [activeEdgeEmbedding_last_successor ctx source u hlast]
        simp [embeddedSuccessorTree, hu, source.active_lastRow_iff hlast, source]

theorem embeddedSuccessorTree_depth
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (v : GridNode (ambientOrder ell)) :
    (embeddedSuccessorTree ctx v).depth ≤ 2 * ell := by
  cases hlocal : embeddedLocalNode hell ctx.currentBox v with
  | none => simp [embeddedSuccessorTree, hlocal]
  | some u =>
      simp only [embeddedSuccessorTree, hlocal]
      split
      next hu => exact embeddedInternalSuccessorTree_depth ctx u hu
      next => simp [two_mul]

/-- The complete encoded target assignment induced by the active-edge embedding. -/
noncomputable def embeddedAssignment
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : Fin (SoPL.Encoding.variableCount ell) → F2) :
    Fin (SoD.Encoding.variableCount (2 * ell)) → F2 :=
  SoD.Encoding.encodeInput
    (activeEdgeEmbedding ctx (SoPL.Encoding.decodeInput ell y))

/-- Compute one encoded target bit from the encoded source assignment. -/
noncomputable def embeddedBitTree
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (i : Fin (SoD.Encoding.variableCount (2 * ell))) :
    DecisionTree (SoPL.Encoding.variableCount ell) F2 :=
  let index := (SoD.Encoding.bitIndexEquiv (2 * ell)).symm i
  (embeddedSuccessorTree ctx index.1).map fun pointer =>
    BinaryPointer.encode pointer index.2

@[simp]
theorem eval_embeddedBitTree
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (i : Fin (SoD.Encoding.variableCount (2 * ell)))
    (y : Fin (SoPL.Encoding.variableCount ell) → F2) :
    (embeddedBitTree ctx i).eval y = embeddedAssignment ctx y i := by
  simp [embeddedBitTree, embeddedAssignment, SoD.Encoding.encodeInput]

theorem embedded_bit_depth
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (i : Fin (SoD.Encoding.variableCount (2 * ell))) :
    (embeddedBitTree ctx i).depth ≤ 2 * ell := by
  simp [embeddedBitTree, embeddedSuccessorTree_depth]

/-- Map a fixed target witness to the corresponding local source witness. -/
noncomputable def solutionMap
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell) :
    SoD.Output (ambientOrder ell) →
      DecisionTree (SoPL.Encoding.variableCount ell)
        (Option (SoPL.Output (localOrder ell)))
  | .inactiveSource => .leaf (some .inactiveSource)
  | .activeLast _ => .leaf none
  | .properSink v =>
      match embeddedLocalNode hell ctx.currentBox v with
      | none => .leaf (some .inactiveSource)
      | some u =>
          if hu : u.IsInternal then
            (SoPL.Encoding.readSuccessor ell u).map fun successor =>
              match successor with
              | none => none
              | some column => some (.properSink (u.next hu column))
          else
            (SoPL.Encoding.readSuccessor ell u).map fun successor =>
              if successor ≠ none then some (.activeLast u) else none

theorem solutionMap_depth
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (o : SoD.Output (ambientOrder ell)) :
    (solutionMap ctx o).depth ≤ ell := by
  cases o with
  | inactiveSource => simp [solutionMap]
  | activeLast => simp [solutionMap]
  | properSink v =>
      cases hlocal : embeddedLocalNode hell ctx.currentBox v with
      | none => simp [solutionMap, hlocal]
      | some u =>
          by_cases hu : u.IsInternal <;> simp [solutionMap, hlocal, hu]

theorem solutionMap_sound
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (o : SoD.Output (ambientOrder ell))
    (y : Fin (SoPL.Encoding.variableCount ell) → F2)
    (sourceOutput : SoPL.Output (localOrder ell))
    (htarget : SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell))
      (activeEdgeEmbedding ctx (SoPL.Encoding.decodeInput ell y)) o)
    (hmap : (solutionMap ctx o).eval y = some sourceOutput) :
    SoPL.Valid (BinaryPointer.order_pos hell)
      (SoPL.Encoding.decodeInput ell y) sourceOutput := by
  let source := SoPL.Encoding.decodeInput ell y
  cases o with
  | inactiveSource =>
      have hout : sourceOutput = .inactiveSource := by
        symm
        simpa [solutionMap] using hmap
      subst sourceOutput
      exact inactiveSource_maps_to_inactiveSource ctx source htarget
  | activeLast u =>
      simp [solutionMap] at hmap
  | properSink v =>
      cases hlocal : embeddedLocalNode hell ctx.currentBox v with
      | none =>
          have hout : sourceOutput = .inactiveSource := by
            symm
            simpa [solutionMap, hlocal] using hmap
          subst sourceOutput
          exact no_outside_solution ctx source
            (embeddedLocalNode_eq_none_iff.mp hlocal) htarget
      | some u =>
          have hv : v = embedNode hell ctx.currentBox u :=
            (embeddedLocalNode_eq_some_iff.mp hlocal).symm
          subst v
          rcases u.internal_or_last with hu | hu
          · obtain ⟨w, hedge, hsink⟩ :=
              (internal_solution_maps_to_properSink ctx source u hu).mp htarget
            have hnext : ∀ h : u.IsInternal, u.next h w.column = w := by
              intro h
              apply Prod.ext
              · apply Fin.ext
                exact hedge.1.symm
              · rfl
            have hdecode :
                BinaryPointer.decode
                    (fun b => y (SoPL.Encoding.successorBit ell u b)) =
                  some w.column := by
              simpa [source, SoPL.Encoding.decodeInput] using hedge.2.1
            have hvalue :
                (solutionMap ctx (.properSink
                  (embedNode hell ctx.currentBox u))).eval y =
                    some (.properSink w) := by
              simpa [solutionMap, hu, hdecode] using
                congrArg (fun v => some (SoPL.Output.properSink v)) (hnext hu)
            have hout : sourceOutput = .properSink w := by
              exact Option.some.inj (hmap.symm.trans hvalue)
            subst sourceOutput
            exact hsink
          · have hactive :=
              (last_row_solution_maps_to_activeLast ctx source u hu).mp htarget
            have hsucc : source.successor u ≠ none :=
              (source.active_lastRow_iff hu).mp hactive
            have hdecode :
                BinaryPointer.decode
                    (fun b => y (SoPL.Encoding.successorBit ell u b)) ≠ none := by
              simpa [source, SoPL.Encoding.decodeInput] using hsucc
            have hvalue :
                (solutionMap ctx (.properSink
                  (embedNode hell ctx.currentBox u))).eval y =
                    some (.activeLast u) := by
              simp [solutionMap, GridNode.not_internal_of_last hu, hdecode]
            have hout : sourceOutput = .activeLast u := by
              exact Option.some.inj (hmap.symm.trans hvalue)
            subst sourceOutput
            exact ⟨hu, hactive⟩

theorem solutionMap_complete
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (o : SoD.Output (ambientOrder ell))
    (y : Fin (SoPL.Encoding.variableCount ell) → F2)
    (htarget : SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell))
      (activeEdgeEmbedding ctx (SoPL.Encoding.decodeInput ell y)) o) :
    ∃ sourceOutput,
      (solutionMap ctx o).eval y = some sourceOutput := by
  let source := SoPL.Encoding.decodeInput ell y
  cases o with
  | inactiveSource => exact ⟨.inactiveSource, by simp [solutionMap]⟩
  | activeLast u => exact (no_activeLast_solution ctx source u htarget).elim
  | properSink v =>
      cases hlocal : embeddedLocalNode hell ctx.currentBox v with
      | none => exact ⟨.inactiveSource, by simp [solutionMap, hlocal]⟩
      | some u =>
          have hv : v = embedNode hell ctx.currentBox u :=
            (embeddedLocalNode_eq_some_iff.mp hlocal).symm
          subst v
          rcases u.internal_or_last with hu | hu
          · obtain ⟨w, hedge, _hsink⟩ :=
              (internal_solution_maps_to_properSink ctx source u hu).mp htarget
            have hnext : ∀ h : u.IsInternal, u.next h w.column = w := by
              intro h
              apply Prod.ext
              · apply Fin.ext
                exact hedge.1.symm
              · rfl
            have hdecode :
                BinaryPointer.decode
                    (fun b => y (SoPL.Encoding.successorBit ell u b)) =
                  some w.column := by
              simpa [source, SoPL.Encoding.decodeInput] using hedge.2.1
            exact ⟨.properSink w, by
              simpa [solutionMap, hu, hdecode] using
                congrArg (fun v => some (SoPL.Output.properSink v)) (hnext hu)⟩
          · have hactive :=
              (last_row_solution_maps_to_activeLast ctx source u hu).mp htarget
            have hsucc : source.successor u ≠ none :=
              (source.active_lastRow_iff hu).mp hactive
            have hdecode :
                BinaryPointer.decode
                    (fun b => y (SoPL.Encoding.successorBit ell u b)) ≠ none := by
              simpa [source, SoPL.Encoding.decodeInput] using hsucc
            exact ⟨.activeLast u, by
              simp [solutionMap, GridNode.not_internal_of_last hu, hdecode]⟩

/-- Gated search for a falsified source clause corresponding to one target clause. -/
noncomputable def clauseSearch
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (C : ↑(SoD.Encoding.searchCNF (2 * ell) (ambientWidth_pos hell))) :
    DecisionTree (SoPL.Encoding.variableCount ell)
      (Option (Clause (SoPL.Encoding.variableCount ell))) :=
  (DecisionTree.checkMappedClause (embeddedBitTree ctx) C.1).bind fun falsified =>
    if falsified then
      (solutionMap ctx (SoD.Encoding.clauseOutput C)).bind fun sourceOutput =>
        match sourceOutput with
        | none => .leaf none
        | some o => (SoPL.Encoding.searchProblem ell hell).acceptingClauseTree o
    else
      .leaf none

theorem clauseSearch_sound
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (C : ↑(SoD.Encoding.searchCNF (2 * ell) (ambientWidth_pos hell)))
    (y : Fin (SoPL.Encoding.variableCount ell) → F2)
    {D : Clause (SoPL.Encoding.variableCount ell)}
    (hsearch : (clauseSearch ctx C).eval y = some D) :
    D ∈ SoPL.Encoding.searchCNF ell hell ∧ D.Falsified y ∧
      C.1.Falsified (embeddedAssignment ctx y) := by
  cases hcheck : (DecisionTree.checkMappedClause (embeddedBitTree ctx) C.1).eval y with
  | false => simp [clauseSearch, hcheck] at hsearch
  | true =>
      cases hsolution : (solutionMap ctx (SoD.Encoding.clauseOutput C)).eval y with
      | none => simp [clauseSearch, hcheck, hsolution] at hsearch
      | some sourceOutput =>
          have haccept :
              ((SoPL.Encoding.searchProblem ell hell).acceptingClauseTree
                sourceOutput).eval y = some D := by
            simpa [clauseSearch, hcheck, hsolution] using hsearch
          have hsound :=
            (SoPL.Encoding.searchProblem ell hell).acceptingClauseTree_sound
              sourceOutput y haccept
          have htarget : C.1.Falsified
              (fun i => (embeddedBitTree ctx i).eval y) :=
            (DecisionTree.eval_checkMappedClause
              (embeddedBitTree ctx) C.1 y).mp hcheck
          exact ⟨(SoPL.Encoding.searchProblem ell hell).acceptingClauseTree_mem_toCNF
              sourceOutput y haccept,
            hsound.2,
            by simpa only [eval_embeddedBitTree] using htarget⟩

theorem clauseSearch_complete
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (C : ↑(SoD.Encoding.searchCNF (2 * ell) (ambientWidth_pos hell)))
    (y : Fin (SoPL.Encoding.variableCount ell) → F2)
    (hC : C.1.Falsified (embeddedAssignment ctx y)) :
    ∃ D, (clauseSearch ctx C).eval y = some D := by
  have htarget : SoD.Valid (BinaryPointer.order_pos (ambientWidth_pos hell))
      (activeEdgeEmbedding ctx (SoPL.Encoding.decodeInput ell y))
      (SoD.Encoding.clauseOutput C) := by
    simpa [embeddedAssignment] using SoD.Encoding.clauseOutput_valid C hC
  obtain ⟨sourceOutput, hsolution⟩ :=
    solutionMap_complete ctx (SoD.Encoding.clauseOutput C) y htarget
  have hsource := solutionMap_sound ctx (SoD.Encoding.clauseOutput C) y
    sourceOutput htarget hsolution
  obtain ⟨D, haccept⟩ :=
    (SoPL.Encoding.searchProblem ell hell).acceptingClauseTree_complete
      sourceOutput y hsource
  refine ⟨D, ?_⟩
  have hcheck :
      (DecisionTree.checkMappedClause (embeddedBitTree ctx) C.1).eval y = true :=
    (DecisionTree.eval_checkMappedClause _ _ _).mpr (by simpa using hC)
  simp [clauseSearch, hcheck, hsolution, haccept]

theorem clauseSearch_depth
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (C : ↑(SoD.Encoding.searchCNF (2 * ell) (ambientWidth_pos hell))) :
    (clauseSearch ctx C).depth ≤ C.1.width * (7 * ell) := by
  let sourceNext := fun sourceOutput : Option (SoPL.Output (localOrder ell)) =>
    match sourceOutput with
    | none => DecisionTree.leaf none
    | some o => (SoPL.Encoding.searchProblem ell hell).acceptingClauseTree o
  have hsourceNext : ∀ sourceOutput, (sourceNext sourceOutput).depth ≤ 4 * ell := by
    intro sourceOutput
    cases sourceOutput with
    | none => simp [sourceNext]
    | some o =>
        exact ((SoPL.Encoding.searchProblem ell hell).acceptingClauseTree_depth_le o).trans
          (SoPL.Encoding.verifier_depth_le ell hell o)
  let checkedNext := fun falsified : Bool =>
    if falsified then
      (solutionMap ctx (SoD.Encoding.clauseOutput C)).bind sourceNext
    else
      DecisionTree.leaf none
  have hcheckedNext : ∀ falsified, (checkedNext falsified).depth ≤ 5 * ell := by
    intro falsified
    cases falsified with
    | false => simp [checkedNext]
    | true =>
        calc
          ((solutionMap ctx (SoD.Encoding.clauseOutput C)).bind sourceNext).depth ≤
              (solutionMap ctx (SoD.Encoding.clauseOutput C)).depth + 4 * ell :=
            DecisionTree.depth_bind_le _ _ hsourceNext
          _ ≤ ell + 4 * ell :=
            Nat.add_le_add_right
              (solutionMap_depth ctx (SoD.Encoding.clauseOutput C)) (4 * ell)
          _ = 5 * ell := by omega
  have houter := DecisionTree.depth_bind_le
    (DecisionTree.checkMappedClause (embeddedBitTree ctx) C.1)
    checkedNext hcheckedNext
  have hcheckDepth := DecisionTree.depth_checkMappedClause_le
    (embeddedBitTree ctx) C.1 (fun i => embedded_bit_depth ctx i)
  have hadd : 5 * ell ≤ C.1.width * (5 * ell) := by
    simpa using Nat.mul_le_mul_right (5 * ell)
      (SoD.Encoding.one_le_width_searchCNF_clause C)
  calc
    (clauseSearch ctx C).depth ≤
        (DecisionTree.checkMappedClause (embeddedBitTree ctx) C.1).depth + 5 * ell := by
      simpa [clauseSearch, checkedNext, sourceNext] using houter
    _ ≤ C.1.width * (2 * ell) + 5 * ell := Nat.add_le_add_right hcheckDepth _
    _ ≤ C.1.width * (2 * ell) + C.1.width * (5 * ell) :=
      Nat.add_le_add_left hadd _
    _ = C.1.width * (7 * ell) := by ring

/-- The active-edge embedding as a concrete bounded-depth formulation. -/
noncomputable def activeEdgeFormulation
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell) :
    DTFormulation
      (SoPL.Encoding.searchCNF ell hell)
      (SoD.Encoding.searchCNF (2 * ell) (ambientWidth_pos hell)) where
  depth := 7 * ell
  inputTree := embeddedBitTree ctx
  inputTree_depth i := (embedded_bit_depth ctx i).trans (by omega)
  clauseSearch := clauseSearch ctx
  clauseSearch_depth := clauseSearch_depth ctx
  clauseSearch_sound C y D h := by
    simpa using clauseSearch_sound ctx C y (D := D) h
  clauseSearch_complete C y h := by
    apply clauseSearch_complete ctx C y
    simpa only [eval_embeddedBitTree] using h

@[simp]
theorem activeEdgeFormulation_depth
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell) :
    (activeEdgeFormulation ctx).depth = 7 * ell :=
  rfl

theorem activeEdgeFormulation_mapInput
    {ell : ℕ} {hell : 0 < ell} (ctx : StageContext ell hell)
    (y : Fin (SoPL.Encoding.variableCount ell) → F2) :
    (activeEdgeFormulation ctx).mapInput y = embeddedAssignment ctx y := by
  funext i
  exact eval_embeddedBitTree ctx i y

end ActiveEdge

end SoD

end Revres
