import Revres.SoPL.ApproxNS.SinkDecomposition

/-!
# Deterministic OR-to-SoPL path reduction

An OR input selects path labels in addition to one always-active planted label. Independent
permutations place those labels in every non-first row. The resulting semantic SoPL input is an
explicit family of disjoint complete paths.
-/

namespace Revres

open Lemma53

namespace SoPL

namespace ApproxNS

/-- The OR input has one bit for every non-planted path label. -/
abbrev ORInput (ell : ℕ) :=
  Fin (BinaryPointer.order ell - 1) → F2

/-- The number of input coordinates equal to one. -/
def hammingWeight {ell : ℕ} (x : ORInput ell) : ℕ :=
  (Finset.univ.filter fun j ↦ x j = 1).card

theorem order_pred_add_one {ell : ℕ} (hell : 0 < ell) :
    BinaryPointer.order ell - 1 + 1 = BinaryPointer.order ell :=
  Nat.sub_add_cancel (BinaryPointer.order_pos hell)

/-- The checked zero label in the positive-order grid. -/
def zeroLabel {ell : ℕ} (hell : 0 < ell) :
    Fin (BinaryPointer.order ell) :=
  ⟨0, BinaryPointer.order_pos hell⟩

/-- Decompose a grid label into the planted zero label or one OR-bit label. -/
def labelCase {ell : ℕ} (hell : 0 < ell) :
    Fin (BinaryPointer.order ell) ≃
      Option (Fin (BinaryPointer.order ell - 1)) :=
  (finCongr (order_pred_add_one hell).symm).trans
    (finSuccEquiv (BinaryPointer.order ell - 1))

@[simp]
theorem labelCase_zero {ell : ℕ} (hell : 0 < ell) :
    labelCase hell (zeroLabel hell) = none := by
  simp [labelCase, zeroLabel]

/-- The nonzero label corresponding to OR coordinate `j`. -/
def labelOfBit {ell : ℕ} (hell : 0 < ell)
    (j : Fin (BinaryPointer.order ell - 1)) :
    Fin (BinaryPointer.order ell) :=
  (labelCase hell).symm (some j)

@[simp]
theorem labelCase_labelOfBit {ell : ℕ} (hell : 0 < ell)
    (j : Fin (BinaryPointer.order ell - 1)) :
    labelCase hell (labelOfBit hell j) = some j :=
  (labelCase hell).apply_symm_apply (some j)

theorem labelOfBit_ne_zero {ell : ℕ} (hell : 0 < ell)
    (j : Fin (BinaryPointer.order ell - 1)) :
    labelOfBit hell j ≠ zeroLabel hell := by
  intro hzero
  have h := congrArg (labelCase hell) hzero
  simp at h

theorem labelOfBit_injective {ell : ℕ} (hell : 0 < ell) :
    Function.Injective (labelOfBit hell) := by
  intro i j hij
  have h := congrArg (labelCase hell) hij
  simpa using h

theorem exists_labelOfBit_of_ne_zero {ell : ℕ} (hell : 0 < ell)
    (c : Fin (BinaryPointer.order ell)) (hc : c ≠ zeroLabel hell) :
    ∃ j, labelOfBit hell j = c := by
  cases hcase : labelCase hell c with
  | none =>
      have hzero : c = zeroLabel hell := (labelCase hell).injective
        (hcase.trans (labelCase_zero hell).symm)
      exact (hc hzero).elim
  | some j =>
      refine ⟨j, (labelCase hell).injective ?_⟩
      rw [labelCase_labelOfBit, hcase]

/-- The planted label is always active; label `j + 1` is active exactly at bit one. -/
def labelActive {ell : ℕ} (hell : 0 < ell) (x : ORInput ell)
    (c : Fin (BinaryPointer.order ell)) : Prop :=
  match labelCase hell c with
  | none => True
  | some j => x j = 1

instance labelActiveDecidable {ell : ℕ} (hell : 0 < ell)
    (x : ORInput ell) (c : Fin (BinaryPointer.order ell)) :
    Decidable (labelActive hell x c) := by
  unfold labelActive
  split <;> infer_instance

@[simp]
theorem labelActive_zero {ell : ℕ} (hell : 0 < ell) (x : ORInput ell) :
    labelActive hell x (zeroLabel hell) := by
  simp [labelActive]

@[simp]
theorem labelActive_labelOfBit {ell : ℕ} (hell : 0 < ell)
    (x : ORInput ell) (j : Fin (BinaryPointer.order ell - 1)) :
    labelActive hell x (labelOfBit hell j) ↔ x j = 1 := by
  simp [labelActive]

/-- The selected path labels. -/
def activeLabels {ell : ℕ} (hell : 0 < ell) (x : ORInput ell) :
    Finset (Fin (BinaryPointer.order ell)) :=
  Finset.univ.filter (labelActive hell x)

@[simp]
theorem mem_activeLabels {ell : ℕ} (hell : 0 < ell) (x : ORInput ell)
    (c : Fin (BinaryPointer.order ell)) :
    c ∈ activeLabels hell x ↔ labelActive hell x c := by
  simp [activeLabels]

theorem activeLabels_eq_insert_image {ell : ℕ} (hell : 0 < ell)
    (x : ORInput ell) :
    activeLabels hell x =
      insert (zeroLabel hell)
        ((Finset.univ.filter fun j ↦ x j = 1).image (labelOfBit hell)) := by
  classical
  ext c
  constructor
  · intro hc
    have hactive := (mem_activeLabels hell x c).mp hc
    by_cases hzero : c = zeroLabel hell
    · simp [hzero]
    · obtain ⟨j, hj⟩ := exists_labelOfBit_of_ne_zero hell c hzero
      rw [Finset.mem_insert]
      exact Or.inr (Finset.mem_image.mpr ⟨j, by
        simp [(labelActive_labelOfBit hell x j).mp (hj ▸ hactive)], hj⟩)
  · intro hc
    rw [Finset.mem_insert] at hc
    rcases hc with hzero | hbit
    · subst c
      exact mem_activeLabels hell x (zeroLabel hell) |>.mpr (labelActive_zero hell x)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hbit
      exact (mem_activeLabels hell x (labelOfBit hell j)).mpr
        ((labelActive_labelOfBit hell x j).mpr (by simpa using hj))

theorem activeLabels_card {ell : ℕ} (hell : 0 < ell) (x : ORInput ell) :
    (activeLabels hell x).card = 1 + hammingWeight x := by
  classical
  rw [activeLabels_eq_insert_image]
  have hzero :
      zeroLabel hell ∉
        (Finset.univ.filter fun j ↦ x j = 1).image (labelOfBit hell) := by
    intro hmem
    obtain ⟨j, _hj, hlabel⟩ := Finset.mem_image.mp hmem
    exact labelOfBit_ne_zero hell j hlabel
  rw [Finset.card_insert_of_notMem hzero,
    Finset.card_image_of_injective _ (labelOfBit_injective hell)]
  simp [hammingWeight, Nat.add_comm]

/-- One permutation of the path labels for every non-first row. -/
abbrev RowPermSeed (n : ℕ) :=
  Fin (n - 1) → Equiv.Perm (Fin n)

noncomputable instance rowPermSeedFintype (n : ℕ) :
    Fintype (RowPermSeed n) :=
  inferInstance

/-- The unpermuted seed. -/
def identitySeed (n : ℕ) : RowPermSeed n :=
  fun _ ↦ Equiv.refl _

/-- The row permutation, with row zero fixed to the identity. -/
def rowPerm {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (r : Fin (BinaryPointer.order ell)) :
    Equiv.Perm (Fin (BinaryPointer.order ell)) :=
  match labelCase hell r with
  | none => Equiv.refl _
  | some j => seed j

@[simp]
theorem rowPerm_zero {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    rowPerm hell seed (zeroLabel hell) = Equiv.refl _ := by
  simp [rowPerm]

@[simp]
theorem rowPerm_labelOfBit {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (j : Fin (BinaryPointer.order ell - 1)) :
    rowPerm hell seed (labelOfBit hell j) = seed j := by
  simp [rowPerm]

/-- The row immediately before the non-first row named by `j`. -/
def previousRow {ell : ℕ} (hell : 0 < ell)
    (j : Fin (BinaryPointer.order ell - 1)) :
    Fin (BinaryPointer.order ell) :=
  Fin.cast (order_pred_add_one hell) (Fin.castSucc j)

@[simp]
theorem previousRow_val {ell : ℕ} (hell : 0 < ell)
    (j : Fin (BinaryPointer.order ell - 1)) :
    (previousRow hell j).val = j.val :=
  rfl

@[simp]
theorem labelOfBit_val {ell : ℕ} (hell : 0 < ell)
    (j : Fin (BinaryPointer.order ell - 1)) :
    (labelOfBit hell j).val = j.val + 1 := by
  simp [labelOfBit, labelCase]

theorem previousRow_next_labelOfBit {ell : ℕ} (hell : 0 < ell)
    (j : Fin (BinaryPointer.order ell - 1)) :
    (previousRow hell j).val + 1 = (labelOfBit hell j).val := by
  simp

/-- The last row of the positive-order grid. -/
def lastRow {ell : ℕ} (hell : 0 < ell) :
    Fin (BinaryPointer.order ell) :=
  Fin.cast (order_pred_add_one hell)
    (Fin.last (BinaryPointer.order ell - 1))

@[simp]
theorem lastRow_val {ell : ℕ} (hell : 0 < ell) :
    (lastRow hell).val = BinaryPointer.order ell - 1 :=
  rfl

theorem lastRow_isLastRow {ell : ℕ} (hell : 0 < ell) :
    GridNode.IsLastRow
      ((lastRow hell, zeroLabel hell) : GridNode (BinaryPointer.order ell)) := by
  unfold GridNode.IsLastRow
  simpa using order_pred_add_one hell

/-- The complete row-permuted path carrying label `c`. -/
def pathOf {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c : Fin (BinaryPointer.order ell)) :
    SoPL.Path (BinaryPointer.order ell) :=
  fun r ↦ rowPerm hell seed r c

/-- The node occupied by label `c` in row `r`. -/
def pathNode {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c r : Fin (BinaryPointer.order ell)) :
    GridNode (BinaryPointer.order ell) :=
  (r, pathOf hell seed c r)

@[simp]
theorem pathNode_row {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c r : Fin (BinaryPointer.order ell)) :
    (pathNode hell seed c r).row = r :=
  rfl

@[simp]
theorem pathNode_column {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c r : Fin (BinaryPointer.order ell)) :
    (pathNode hell seed c r).column = pathOf hell seed c r :=
  rfl

@[simp]
theorem pathOf_contains_pathNode {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c r : Fin (BinaryPointer.order ell)) :
    (pathOf hell seed c).Contains (pathNode hell seed c r) :=
  rfl

/-- The last-row endpoint of label `c`. -/
def pathEndpoint {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c : Fin (BinaryPointer.order ell)) :
    GridNode (BinaryPointer.order ell) :=
  pathNode hell seed c (lastRow hell)

/-- The endpoint of the always-active zero label. -/
def plantedSink {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    GridNode (BinaryPointer.order ell) :=
  pathEndpoint hell seed (zeroLabel hell)

theorem pathEndpoint_isLastRow {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c : Fin (BinaryPointer.order ell)) :
    (pathEndpoint hell seed c).IsLastRow := by
  unfold pathEndpoint pathNode GridNode.IsLastRow
  simpa using order_pred_add_one hell

theorem pathOf_apply_injective {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (r : Fin (BinaryPointer.order ell)) :
    Function.Injective (fun c ↦ pathOf hell seed c r) :=
  (rowPerm hell seed r).injective

theorem pathOf_injective {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    Function.Injective (pathOf hell seed) := by
  intro c d hcd
  exact pathOf_apply_injective hell seed (zeroLabel hell)
    (congrFun hcd (zeroLabel hell))

theorem pathEndpoint_injective {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    Function.Injective (pathEndpoint hell seed) := by
  intro c d hcd
  exact pathOf_apply_injective hell seed (lastRow hell)
    (congrArg Prod.snd hcd)

theorem pathOf_zero_contains_distinguished {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    (pathOf hell seed (zeroLabel hell)).Contains
      (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
  change rowPerm hell seed (zeroLabel hell) (zeroLabel hell) = zeroLabel hell
  simp

/-- The unique path label occupying node `u`. -/
def nodeLabel {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : GridNode (BinaryPointer.order ell)) :
    Fin (BinaryPointer.order ell) :=
  (rowPerm hell seed u.row).symm u.column

@[simp]
theorem nodeLabel_pathNode {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c r : Fin (BinaryPointer.order ell)) :
    nodeLabel hell seed (pathNode hell seed c r) = c :=
  (rowPerm hell seed r).symm_apply_apply c

@[simp]
theorem nodeLabel_pathEndpoint {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c : Fin (BinaryPointer.order ell)) :
    nodeLabel hell seed (pathEndpoint hell seed c) = c := by
  exact nodeLabel_pathNode hell seed c (lastRow hell)

theorem pathOf_contains_iff_nodeLabel_eq {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c : Fin (BinaryPointer.order ell))
    (u : GridNode (BinaryPointer.order ell)) :
    (pathOf hell seed c).Contains u ↔ nodeLabel hell seed u = c := by
  constructor
  · intro hcontains
    unfold nodeLabel
    apply (rowPerm hell seed u.row).injective
    rw [(rowPerm hell seed u.row).apply_symm_apply]
    exact hcontains.symm
  · intro hlabel
    unfold Path.Contains pathOf
    rw [← hlabel, nodeLabel]
    exact (rowPerm hell seed u.row).apply_symm_apply u.column

/-- The semantic SoPL input formed by the selected row-permuted paths. -/
noncomputable def reductionInput {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    SoPL.Input (BinaryPointer.order ell) where
  successor u :=
    let c := nodeLabel hell seed u
    if _hactive : labelActive hell x c then
      if hu : u.IsInternal then
        some (pathOf hell seed c ⟨u.row.val + 1, hu⟩)
      else
        some u.column
    else
      none
  predecessor u :=
    let c := nodeLabel hell seed u
    if _hactive : labelActive hell x c then
      match labelCase hell u.row with
      | none => none
      | some j => some (pathOf hell seed c (previousRow hell j))
    else
      none

@[simp]
theorem reductionInput_successor_pathNode_of_active_internal
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (c r : Fin (BinaryPointer.order ell))
    (hactive : labelActive hell x c)
    (hr : (pathNode hell seed c r).IsInternal) :
    (reductionInput hell seed x).successor (pathNode hell seed c r) =
      some (pathOf hell seed c ⟨r.val + 1, hr⟩) := by
  simp only [reductionInput, nodeLabel_pathNode]
  rw [dif_pos hactive, dif_pos hr]
  congr 2

@[simp]
theorem reductionInput_successor_pathNode_of_inactive
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (c r : Fin (BinaryPointer.order ell))
    (hinactive : ¬labelActive hell x c) :
    (reductionInput hell seed x).successor (pathNode hell seed c r) = none := by
  simp [reductionInput, hinactive]

@[simp]
theorem reductionInput_predecessor_pathNode_zero
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (c : Fin (BinaryPointer.order ell))
    (hactive : labelActive hell x c) :
    (reductionInput hell seed x).predecessor
      (pathNode hell seed c (zeroLabel hell)) = none := by
  simp only [reductionInput, nodeLabel_pathNode]
  rw [dif_pos hactive]
  simp [pathNode]

@[simp]
theorem reductionInput_predecessor_pathNode_labelOfBit
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (c : Fin (BinaryPointer.order ell))
    (j : Fin (BinaryPointer.order ell - 1))
    (hactive : labelActive hell x c) :
    (reductionInput hell seed x).predecessor
      (pathNode hell seed c (labelOfBit hell j)) =
        some (pathOf hell seed c (previousRow hell j)) := by
  simp only [reductionInput, nodeLabel_pathNode]
  rw [dif_pos hactive]
  simp [pathNode]

@[simp]
theorem reductionInput_predecessor_pathNode_of_inactive
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (c r : Fin (BinaryPointer.order ell))
    (hinactive : ¬labelActive hell x c) :
    (reductionInput hell seed x).predecessor (pathNode hell seed c r) = none := by
  simp [reductionInput, hinactive]

theorem reductionInput_successor_pathEndpoint_of_active
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (c : Fin (BinaryPointer.order ell))
    (hactive : labelActive hell x c) :
    (reductionInput hell seed x).successor (pathEndpoint hell seed c) =
      some (pathEndpoint hell seed c).column := by
  have hnotInternal : ¬(pathEndpoint hell seed c).IsInternal :=
    GridNode.not_internal_of_last (pathEndpoint_isLastRow hell seed c)
  simp only [reductionInput, nodeLabel_pathEndpoint]
  rw [dif_pos hactive, dif_neg hnotInternal]

/-- The finite path family selected by the OR input. -/
noncomputable def reductionPaths {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    Finset (SoPL.Path (BinaryPointer.order ell)) := by
  classical
  exact (activeLabels hell x).image (pathOf hell seed)

theorem mem_reductionPaths {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (p : SoPL.Path (BinaryPointer.order ell)) :
    p ∈ reductionPaths hell seed x ↔
      ∃ c ∈ activeLabels hell x, pathOf hell seed c = p := by
  classical
  simp [reductionPaths]

/-- Active edges are exactly consecutive edges on selected permuted paths. -/
theorem reductionInput_activeEdge_iff
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (u v : GridNode (BinaryPointer.order ell)) :
    (reductionInput hell seed x).ActiveEdge u v ↔
      ∃ p ∈ reductionPaths hell seed x, p.Edge u v := by
  constructor
  · intro hedge
    let c := nodeLabel hell seed u
    have huinternal : u.IsInternal := GridNode.nextRow_internal hedge.1
    have hactive : labelActive hell x c := by
      by_contra hinactive
      have hsucc := hedge.2.1
      simp [reductionInput, c, hinactive] at hsucc
    have hmember : pathOf hell seed c ∈ reductionPaths hell seed x :=
      (mem_reductionPaths hell seed x _).mpr
        ⟨c, (mem_activeLabels hell x c).mpr hactive, rfl⟩
    have hucontains : (pathOf hell seed c).Contains u :=
      (pathOf_contains_iff_nodeLabel_eq hell seed c u).mpr rfl
    let nextRow : Fin (BinaryPointer.order ell) :=
      ⟨u.row.val + 1, huinternal⟩
    have hnextRow : nextRow = v.row := by
      apply Fin.ext
      exact hedge.1.symm
    have hsucc : some (pathOf hell seed c nextRow) = some v.column := by
      simpa [reductionInput, c, hactive, huinternal, nextRow] using hedge.2.1
    have hvcontains : (pathOf hell seed c).Contains v := by
      unfold Path.Contains
      rw [← hnextRow]
      exact Option.some.inj hsucc
    exact ⟨pathOf hell seed c, hmember, hedge.1, hucontains, hvcontains⟩
  · rintro ⟨p, hp, hpedge⟩
    obtain ⟨c, hcactive, rfl⟩ := (mem_reductionPaths hell seed x p).mp hp
    have hactive : labelActive hell x c :=
      (mem_activeLabels hell x c).mp hcactive
    have hlabelu : nodeLabel hell seed u = c :=
      (pathOf_contains_iff_nodeLabel_eq hell seed c u).mp hpedge.2.1
    have hlabelv : nodeLabel hell seed v = c :=
      (pathOf_contains_iff_nodeLabel_eq hell seed c v).mp hpedge.2.2
    have huinternal : u.IsInternal := GridNode.nextRow_internal hpedge.1
    have hnextRow :
        (⟨u.row.val + 1, huinternal⟩ : Fin (BinaryPointer.order ell)) = v.row := by
      apply Fin.ext
      exact hpedge.1.symm
    refine ⟨hpedge.1, ?_, ?_⟩
    · have hvcolumn : pathOf hell seed c v.row = v.column := hpedge.2.2
      simp only [reductionInput]
      rw [hlabelu, dif_pos hactive, dif_pos huinternal]
      congr 1
      rw [hnextRow]
      exact hvcolumn
    · have hvnotzero : v.row ≠ zeroLabel hell := by
        intro hvzero
        have hrow := hpedge.1
        unfold GridNode.NextRow at hrow
        rw [hvzero] at hrow
        simp [zeroLabel] at hrow
      obtain ⟨j, hj⟩ := exists_labelOfBit_of_ne_zero hell v.row hvnotzero
      have hprevious : previousRow hell j = u.row := by
        apply Fin.ext
        change j.val = u.row.val
        have hjval : j.val + 1 = v.row.val := by
          calc
            j.val + 1 = (labelOfBit hell j).val := (labelOfBit_val hell j).symm
            _ = v.row.val := congrArg Fin.val hj
        have hrow : v.row.val = u.row.val + 1 := hpedge.1
        omega
      simp only [reductionInput]
      rw [hlabelv, dif_pos hactive]
      rw [← hj]
      simp only [labelCase_labelOfBit]
      rw [hprevious]
      congr 1
      exact hpedge.2.1

theorem reductionInput_active_last_iff_labelActive
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    {u : GridNode (BinaryPointer.order ell)} (hlast : u.IsLastRow) :
    (reductionInput hell seed x).Active u ↔
      labelActive hell x (nodeLabel hell seed u) := by
  rw [(reductionInput hell seed x).active_lastRow_iff hlast]
  by_cases hactive : labelActive hell x (nodeLabel hell seed u)
  · have hnotInternal := GridNode.not_internal_of_last hlast
    simp [reductionInput, hactive, hnotInternal]
  · simp [reductionInput, hactive]

/-- Last-row activity is exactly coverage by a selected path. -/
theorem reductionInput_activeLast_iff
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (u : GridNode (BinaryPointer.order ell)) (hlast : u.IsLastRow) :
    (reductionInput hell seed x).Active u ↔
      ∃ p ∈ reductionPaths hell seed x, p.Contains u := by
  rw [reductionInput_active_last_iff_labelActive hell seed x hlast]
  constructor
  · intro hactive
    let c := nodeLabel hell seed u
    exact ⟨pathOf hell seed c,
      (mem_reductionPaths hell seed x _).mpr
        ⟨c, (mem_activeLabels hell x c).mpr hactive, rfl⟩,
      (pathOf_contains_iff_nodeLabel_eq hell seed c u).mpr rfl⟩
  · rintro ⟨p, hp, hcontains⟩
    obtain ⟨c, hcactive, rfl⟩ := (mem_reductionPaths hell seed x p).mp hp
    have hlabel := (pathOf_contains_iff_nodeLabel_eq hell seed c u).mp hcontains
    simpa [hlabel] using (mem_activeLabels hell x c).mp hcactive

/-- The selected permuted paths form an explicit path-family witness. -/
noncomputable def reductionPathFamilyWitness
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    SoPL.PathFamilyWitness (BinaryPointer.order_pos hell)
      (reductionInput hell seed x) where
  paths := reductionPaths hell seed x
  pairwiseDisjoint := by
    intro p hp q hq hpq r
    obtain ⟨c, _hc, rfl⟩ := (mem_reductionPaths hell seed x p).mp hp
    obtain ⟨d, _hd, rfl⟩ := (mem_reductionPaths hell seed x q).mp hq
    intro heq
    have hcd : c = d := pathOf_apply_injective hell seed r heq
    subst d
    exact hpq rfl
  activeEdge_iff := reductionInput_activeEdge_iff hell seed x
  activeLast_iff := reductionInput_activeLast_iff hell seed x
  distinguished := by
    refine ⟨pathOf hell seed (zeroLabel hell), ?_, ?_⟩
    · exact (mem_reductionPaths hell seed x _).mpr
        ⟨zeroLabel hell,
          (mem_activeLabels hell x _).mpr (labelActive_zero hell x), rfl⟩
    · exact pathOf_zero_contains_distinguished hell seed

theorem reduction_isPathFamily
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    SoPL.IsPathFamily (BinaryPointer.order_pos hell)
      (reductionInput hell seed x) :=
  ⟨reductionPathFamilyWitness hell seed x⟩

theorem encoded_reduction_isPathFamily
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    SoPL.IsEncodedPathFamily ell hell
      (Encoding.encodeInput ell (reductionInput hell seed x)) := by
  change SoPL.IsPathFamily (BinaryPointer.order_pos hell)
    (Encoding.decodeInput ell
      (Encoding.encodeInput ell (reductionInput hell seed x)))
  rw [Encoding.decodeInput_encodeInput]
  exact reduction_isPathFamily hell seed x

/-- The unpermuted construction is the identity-seed specialization. -/
noncomputable def unpermutedInput {ell : ℕ} (hell : 0 < ell)
    (x : ORInput ell) : SoPL.Input (BinaryPointer.order ell) :=
  reductionInput hell (identitySeed _) x

theorem unpermuted_isPathFamily
    {ell : ℕ} (hell : 0 < ell) (x : ORInput ell) :
    SoPL.IsPathFamily (BinaryPointer.order_pos hell)
      (unpermutedInput hell x) :=
  reduction_isPathFamily hell (identitySeed _) x

theorem row_eq_lastRow_of_isLastRow
    {ell : ℕ} (hell : 0 < ell)
    {u : GridNode (BinaryPointer.order ell)} (hlast : u.IsLastRow) :
    u.row = lastRow hell := by
  apply Fin.ext
  exact Nat.add_right_cancel (hlast.trans (order_pred_add_one hell).symm)

/-- The planted endpoint is an active last-row node for every OR input. -/
theorem plantedSink_activeLast
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    (plantedSink hell seed).IsLastRow ∧
      (reductionInput hell seed x).Active (plantedSink hell seed) := by
  have hlast : (plantedSink hell seed).IsLastRow :=
    pathEndpoint_isLastRow hell seed (zeroLabel hell)
  refine ⟨hlast, (reductionInput_active_last_iff_labelActive
    hell seed x hlast).mpr ?_⟩
  simp [plantedSink]

theorem plantedSink_mem_activeLastSet
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    plantedSink hell seed ∈
      Encoding.activeLastSet
        (Encoding.encodeInput ell (reductionInput hell seed x)) := by
  rw [Encoding.mem_activeLastSet, Encoding.decodeInput_encodeInput]
  exact plantedSink_activeLast hell seed x

/-- Active last-row nodes are exactly the endpoints of selected labels. -/
theorem activeLastSet_encode_reduction
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    Encoding.activeLastSet
        (Encoding.encodeInput ell (reductionInput hell seed x)) =
      (activeLabels hell x).image (pathEndpoint hell seed) := by
  classical
  ext u
  rw [Encoding.mem_activeLastSet, Encoding.decodeInput_encodeInput]
  constructor
  · rintro ⟨hlast, hactive⟩
    obtain ⟨p, hp, hcontains⟩ :=
      (reductionInput_activeLast_iff hell seed x u hlast).mp hactive
    obtain ⟨c, hc, rfl⟩ := (mem_reductionPaths hell seed x p).mp hp
    have hrow : u.row = lastRow hell := row_eq_lastRow_of_isLastRow hell hlast
    have hendpoint : pathEndpoint hell seed c = u := by
      apply Prod.ext
      · exact hrow.symm
      · change pathOf hell seed c (lastRow hell) = u.column
        rw [← hrow]
        exact hcontains
    exact Finset.mem_image.mpr ⟨c, hc, hendpoint⟩
  · intro hmem
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hmem
    have hlast := pathEndpoint_isLastRow hell seed c
    refine ⟨hlast, (reductionInput_active_last_iff_labelActive
      hell seed x hlast).mpr ?_⟩
    simpa using (mem_activeLabels hell x c).mp hc

theorem activeLastSet_card
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell) :
    (Encoding.activeLastSet
      (Encoding.encodeInput ell (reductionInput hell seed x))).card =
        1 + hammingWeight x := by
  classical
  rw [activeLastSet_encode_reduction,
    Finset.card_image_of_injective _ (pathEndpoint_injective hell seed),
    activeLabels_card]

theorem activeLastSet_card_eq_one_of_hammingWeight_eq_zero
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (hzero : hammingWeight x = 0) :
    (Encoding.activeLastSet
      (Encoding.encodeInput ell (reductionInput hell seed x))).card = 1 := by
  rw [activeLastSet_card hell seed x, hzero]

theorem two_le_activeLastSet_card_of_hammingWeight_pos
    {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (hpos : 0 < hammingWeight x) :
    2 ≤ (Encoding.activeLastSet
      (Encoding.encodeInput ell (reductionInput hell seed x))).card := by
  rw [activeLastSet_card hell seed x]
  omega

end ApproxNS

end SoPL

end Revres
