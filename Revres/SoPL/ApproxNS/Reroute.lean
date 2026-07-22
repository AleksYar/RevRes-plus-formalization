import Revres.SoPL.ApproxNS.RowLocality

/-!
# Rerouting by an active-label transposition

Below a checked cut, precomposing every row permutation by the swap of the planted label and one
selected active label reroutes the two paths across the cut. The physical path family is unchanged
away from the crossing records, and applying the same rerouting twice restores the seed.
-/

namespace Revres

open Lemma53

namespace SoPL

namespace ApproxNS

variable {ell : ℕ} {x : ORInput ell}

/-- Swap the planted label with one selected active label. -/
def rerouteLabelPerm (hell : 0 < ell) (a : ↑(activeLabels hell x)) :
    Equiv.Perm (Fin (BinaryPointer.order ell)) :=
  Equiv.swap (zeroLabel hell) a.1

theorem labelActive_rerouteLabelPerm_iff
    (hell : 0 < ell) (a : ↑(activeLabels hell x))
    (c : Fin (BinaryPointer.order ell)) :
    labelActive hell x (rerouteLabelPerm hell a c) ↔
      labelActive hell x c := by
  have ha : labelActive hell x a.1 :=
    (mem_activeLabels hell x a.1).mp a.2
  by_cases hzero : c = zeroLabel hell
  · subst c
    rw [rerouteLabelPerm, Equiv.swap_apply_left]
    exact iff_of_true ha (labelActive_zero hell x)
  by_cases haeq : c = a.1
  · subst c
    rw [rerouteLabelPerm, Equiv.swap_apply_right]
    exact iff_of_true (labelActive_zero hell x) ha
  · rw [rerouteLabelPerm, Equiv.swap_apply_of_ne_of_ne hzero haeq]

@[simp]
theorem rerouteLabelPerm_apply_self
    (hell : 0 < ell) (a : ↑(activeLabels hell x))
    (c : Fin (BinaryPointer.order ell)) :
    rerouteLabelPerm hell a (rerouteLabelPerm hell a c) = c := by
  exact Equiv.swap_apply_self _ _ _

/-- Precompose every row at or below `cut.upper` by the active-label swap. -/
noncomputable def rerouteSeed
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    RowPermSeed (BinaryPointer.order ell) := fun j ↦
  if cut.upper.val ≤ (labelOfBit hell j).val then
    (rerouteLabelPerm hell a).trans (seed j)
  else
    seed j

@[simp]
theorem rerouteSeed_apply_of_upper_le
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (j : Fin (BinaryPointer.order ell - 1))
    (hrow : cut.upper.val ≤ (labelOfBit hell j).val) :
    rerouteSeed hell cut a seed j =
      (rerouteLabelPerm hell a).trans (seed j) := by
  rw [rerouteSeed, if_pos hrow]

@[simp]
theorem rerouteSeed_apply_of_lt_upper
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (j : Fin (BinaryPointer.order ell - 1))
    (hrow : (labelOfBit hell j).val < cut.upper.val) :
    rerouteSeed hell cut a seed j = seed j := by
  rw [rerouteSeed, if_neg (Nat.not_le.mpr hrow)]

theorem rowPerm_rerouteSeed_of_lt_upper
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (r : Fin (BinaryPointer.order ell))
    (hrow : r.val < cut.upper.val) :
    rowPerm hell (rerouteSeed hell cut a seed) r =
      rowPerm hell seed r := by
  by_cases hzero : r = zeroLabel hell
  · subst r
    simp
  · obtain ⟨j, rfl⟩ := exists_labelOfBit_of_ne_zero hell r hzero
    rw [rowPerm_labelOfBit, rowPerm_labelOfBit,
      rerouteSeed_apply_of_lt_upper hell cut a seed j hrow]

theorem rowPerm_rerouteSeed_of_upper_le
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (r : Fin (BinaryPointer.order ell))
    (hrow : cut.upper.val ≤ r.val) :
    rowPerm hell (rerouteSeed hell cut a seed) r =
      (rerouteLabelPerm hell a).trans (rowPerm hell seed r) := by
  have hupper_pos : 0 < cut.upper.val := by
    have hlower := cut.lower_pos
    simp only [InteriorCut.upper_val]
    omega
  have hzero : r ≠ zeroLabel hell := by
    intro hr
    subst r
    simp [zeroLabel] at hrow
  obtain ⟨j, rfl⟩ := exists_labelOfBit_of_ne_zero hell r hzero
  rw [rowPerm_labelOfBit, rowPerm_labelOfBit,
    rerouteSeed_apply_of_upper_le hell cut a seed j hrow]

theorem pathOf_rerouteSeed_of_lt_upper
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c r : Fin (BinaryPointer.order ell))
    (hrow : r.val < cut.upper.val) :
    pathOf hell (rerouteSeed hell cut a seed) c r =
      pathOf hell seed c r := by
  change rowPerm hell (rerouteSeed hell cut a seed) r c = rowPerm hell seed r c
  rw [rowPerm_rerouteSeed_of_lt_upper hell cut a seed r hrow]

theorem pathOf_rerouteSeed_of_upper_le
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (c r : Fin (BinaryPointer.order ell))
    (hrow : cut.upper.val ≤ r.val) :
    pathOf hell (rerouteSeed hell cut a seed) c r =
      pathOf hell seed (rerouteLabelPerm hell a c) r := by
  change rowPerm hell (rerouteSeed hell cut a seed) r c =
    rowPerm hell seed r (rerouteLabelPerm hell a c)
  rw [rowPerm_rerouteSeed_of_upper_le hell cut a seed r hrow]
  rfl

private theorem cut_upper_le_lastRow
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell)) :
    cut.upper.val ≤ (lastRow hell).val := by
  have hcut := cut.upper_not_last
  have horder := BinaryPointer.order_pos hell
  simp only [InteriorCut.upper_val, lastRow_val]
  omega

theorem planted_endpoint_becomes_selected_endpoint
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    plantedSink hell seed =
      pathEndpoint hell (rerouteSeed hell cut a seed) a.1 := by
  apply Prod.ext
  · rfl
  · change pathOf hell seed (zeroLabel hell) (lastRow hell) =
      pathOf hell (rerouteSeed hell cut a seed) a.1 (lastRow hell)
    rw [pathOf_rerouteSeed_of_upper_le hell cut a seed a.1 (lastRow hell)
      (cut_upper_le_lastRow hell cut)]
    simp [rerouteLabelPerm]

theorem rerouted_planted_endpoint_eq_selected_endpoint
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    plantedSink hell (rerouteSeed hell cut a seed) =
      pathEndpoint hell seed a.1 := by
  apply Prod.ext
  · rfl
  · change pathOf hell (rerouteSeed hell cut a seed) (zeroLabel hell) (lastRow hell) =
      pathOf hell seed a.1 (lastRow hell)
    rw [pathOf_rerouteSeed_of_upper_le hell cut a seed (zeroLabel hell) (lastRow hell)
      (cut_upper_le_lastRow hell cut)]
    simp [rerouteLabelPerm]

theorem nodeLabel_rerouteSeed_of_lt_upper
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell)
    (hrow : u.row.val < cut.upper.val) :
    nodeLabel hell (rerouteSeed hell cut a seed) u =
      nodeLabel hell seed u := by
  unfold nodeLabel
  rw [rowPerm_rerouteSeed_of_lt_upper hell cut a seed u.row hrow]

theorem nodeLabel_rerouteSeed_of_upper_le
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell)
    (hrow : cut.upper.val ≤ u.row.val) :
    nodeLabel hell (rerouteSeed hell cut a seed) u =
      rerouteLabelPerm hell a (nodeLabel hell seed u) := by
  unfold nodeLabel
  rw [rowPerm_rerouteSeed_of_upper_le hell cut a seed u.row hrow]
  simp [rerouteLabelPerm]

theorem rerouteInput_successor_eq_of_row_ne_lower
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell) (hrow : u.row ≠ cut.lower) :
    (reductionInput hell (rerouteSeed hell cut a seed) x).successor u =
      (reductionInput hell seed x).successor u := by
  by_cases habove : u.row.val < cut.upper.val
  · have hneval : u.row.val ≠ cut.lower.val := by
      intro hval
      exact hrow (Fin.ext hval)
    have hlower : u.row.val < cut.lower.val := by
      simp only [InteriorCut.upper_val] at habove
      omega
    simp only [reductionInput,
      nodeLabel_rerouteSeed_of_lt_upper hell cut a seed u habove]
    by_cases hactive : labelActive hell x (nodeLabel hell seed u)
    · rw [dif_pos hactive, dif_pos hactive]
      by_cases hu : u.IsInternal
      · rw [dif_pos hu, dif_pos hu]
        have hnext :
            (⟨u.row.val + 1, hu⟩ : Fin (BinaryPointer.order ell)).val <
              cut.upper.val := by
          change u.row.val + 1 < cut.upper.val
          simp only [InteriorCut.upper_val]
          omega
        rw [pathOf_rerouteSeed_of_lt_upper hell cut a seed _ _ hnext]
      · rw [dif_neg hu, dif_neg hu]
    · rw [dif_neg hactive, dif_neg hactive]
  · have hbelow : cut.upper.val ≤ u.row.val := Nat.le_of_not_gt habove
    simp only [reductionInput,
      nodeLabel_rerouteSeed_of_upper_le hell cut a seed u hbelow]
    have hactive_iff := labelActive_rerouteLabelPerm_iff hell a
      (nodeLabel hell seed u)
    by_cases hactive : labelActive hell x (nodeLabel hell seed u)
    · have hactive' :
          labelActive hell x (rerouteLabelPerm hell a (nodeLabel hell seed u)) :=
        hactive_iff.mpr hactive
      rw [dif_pos hactive', dif_pos hactive]
      by_cases hu : u.IsInternal
      · rw [dif_pos hu, dif_pos hu]
        have hnext :
            cut.upper.val ≤
              (⟨u.row.val + 1, hu⟩ : Fin (BinaryPointer.order ell)).val := by
          change cut.upper.val ≤ u.row.val + 1
          omega
        rw [pathOf_rerouteSeed_of_upper_le hell cut a seed _ _ hnext]
        simp
      · rw [dif_neg hu, dif_neg hu]
    · have hactive' :
          ¬labelActive hell x (rerouteLabelPerm hell a (nodeLabel hell seed u)) :=
        fun h ↦ hactive (hactive_iff.mp h)
      rw [dif_neg hactive', dif_neg hactive]

theorem rerouteInput_predecessor_eq_of_row_ne_upper
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell) (hrow : u.row ≠ cut.upper) :
    (reductionInput hell (rerouteSeed hell cut a seed) x).predecessor u =
      (reductionInput hell seed x).predecessor u := by
  by_cases habove : u.row.val < cut.upper.val
  · simp only [reductionInput,
      nodeLabel_rerouteSeed_of_lt_upper hell cut a seed u habove]
    by_cases hactive : labelActive hell x (nodeLabel hell seed u)
    · rw [dif_pos hactive, dif_pos hactive]
      cases hcase : labelCase hell u.row with
      | none => simp
      | some j =>
          have hurow : labelOfBit hell j = u.row := by
            apply (labelCase hell).injective
            exact hcase.symm
          have hprevious : (previousRow hell j).val < cut.upper.val := by
            have huval := congrArg Fin.val hurow
            simp only [labelOfBit_val, previousRow_val] at huval ⊢
            omega
          simp only [Option.some.injEq]
          change pathOf hell (rerouteSeed hell cut a seed)
              (nodeLabel hell seed u) (previousRow hell j) =
            pathOf hell seed (nodeLabel hell seed u) (previousRow hell j)
          exact pathOf_rerouteSeed_of_lt_upper hell cut a seed _ _ hprevious
    · rw [dif_neg hactive, dif_neg hactive]
  · have hbelow : cut.upper.val ≤ u.row.val := Nat.le_of_not_gt habove
    have hneval : u.row.val ≠ cut.upper.val := by
      intro hval
      exact hrow (Fin.ext hval)
    have hstrict : cut.upper.val < u.row.val := lt_of_le_of_ne hbelow (Ne.symm hneval)
    have hupper_pos : 0 < cut.upper.val := by
      have hlower := cut.lower_pos
      simp only [InteriorCut.upper_val]
      omega
    have huzero : u.row ≠ zeroLabel hell := by
      intro hu
      have hzero : (zeroLabel hell).val = 0 := rfl
      rw [hu, hzero] at hbelow
      omega
    obtain ⟨j, hurow⟩ := exists_labelOfBit_of_ne_zero hell u.row huzero
    have hcase : labelCase hell u.row = some j := by
      rw [← hurow]
      simp
    have hprevious : cut.upper.val ≤ (previousRow hell j).val := by
      have huval := congrArg Fin.val hurow
      simp only [labelOfBit_val, previousRow_val] at huval ⊢
      omega
    simp only [reductionInput,
      nodeLabel_rerouteSeed_of_upper_le hell cut a seed u hbelow]
    have hactive_iff := labelActive_rerouteLabelPerm_iff hell a
      (nodeLabel hell seed u)
    by_cases hactive : labelActive hell x (nodeLabel hell seed u)
    · have hactive' :
          labelActive hell x (rerouteLabelPerm hell a (nodeLabel hell seed u)) :=
        hactive_iff.mpr hactive
      rw [dif_pos hactive', dif_pos hactive, hcase]
      simp only [Option.some.injEq]
      change pathOf hell (rerouteSeed hell cut a seed)
          (rerouteLabelPerm hell a (nodeLabel hell seed u)) (previousRow hell j) =
        pathOf hell seed (nodeLabel hell seed u) (previousRow hell j)
      rw [pathOf_rerouteSeed_of_upper_le hell cut a seed _ _ hprevious]
      simp
    · have hactive' :
          ¬labelActive hell x (rerouteLabelPerm hell a (nodeLabel hell seed u)) :=
        fun h ↦ hactive (hactive_iff.mp h)
      rw [dif_neg hactive', dif_neg hactive]

theorem rerouteInput_eq_outside_cut_rows
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell)
    (hlower : u.row ≠ cut.lower)
    (hupper : u.row ≠ cut.upper) :
    ((reductionInput hell (rerouteSeed hell cut a seed) x).successor u =
      (reductionInput hell seed x).successor u) ∧
    ((reductionInput hell (rerouteSeed hell cut a seed) x).predecessor u =
      (reductionInput hell seed x).predecessor u) :=
  ⟨rerouteInput_successor_eq_of_row_ne_lower hell cut a seed u hlower,
    rerouteInput_predecessor_eq_of_row_ne_upper hell cut a seed u hupper⟩

theorem rerouteInput_activeEdge_iff_of_source_row_ne_lower
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u v : Encoding.Node ell) (hrow : u.row ≠ cut.lower) :
    (reductionInput hell (rerouteSeed hell cut a seed) x).ActiveEdge u v ↔
      (reductionInput hell seed x).ActiveEdge u v := by
  by_cases hnext : u.NextRow v
  · have hvrow : v.row ≠ cut.upper := by
      intro hv
      have hvval := congrArg Fin.val hv
      have hnextval : v.row.val = u.row.val + 1 := hnext
      simp only [InteriorCut.upper_val] at hvval
      apply hrow
      apply Fin.ext
      omega
    unfold SoPL.Input.ActiveEdge
    rw [rerouteInput_successor_eq_of_row_ne_lower hell cut a seed u hrow,
      rerouteInput_predecessor_eq_of_row_ne_upper hell cut a seed v hvrow]
  · simp [SoPL.Input.ActiveEdge, hnext]

/-- The encoded Boolean assignment produced by one reduction seed. -/
noncomputable def reductionAssignment
    (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (x : ORInput ell) :
    Fin (Encoding.variableCount ell) → F2 :=
  Encoding.encodeInput ell (reductionInput hell seed x)

@[simp]
theorem reductionAssignment_apply
    (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (x : ORInput ell)
    (i : Fin (Encoding.variableCount ell)) :
    reductionAssignment hell seed x i =
      Encoding.encodeInput ell (reductionInput hell seed x) i :=
  rfl

theorem reductionAssignment_reroute_eq_of_row_ne
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (i : Fin (Encoding.variableCount ell))
    (hlower : Encoding.rowOfBit ell i ≠ cut.lower)
    (hupper : Encoding.rowOfBit ell i ≠ cut.upper) :
    reductionAssignment hell (rerouteSeed hell cut a seed) x i =
      reductionAssignment hell seed x i := by
  let index := (Encoding.bitIndexEquiv ell).symm i
  have hlower' : index.1.row ≠ cut.lower := by
    intro h
    exact hlower (by simpa [Encoding.rowOfBit, index] using h)
  have hupper' : index.1.row ≠ cut.upper := by
    intro h
    exact hupper (by simpa [Encoding.rowOfBit, index] using h)
  simp only [reductionAssignment, Encoding.encodeInput]
  by_cases hkind : index.2.1 = 0
  · simp only [index, hkind, if_pos]
    rw [rerouteInput_successor_eq_of_row_ne_lower hell cut a seed index.1 hlower']
  · simp only [index, hkind]
    rw [rerouteInput_predecessor_eq_of_row_ne_upper hell cut a seed index.1 hupper']
    simp [index]

theorem reroute_changed_bit_rows
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (i : Fin (Encoding.variableCount ell))
    (hchange :
      reductionAssignment hell (rerouteSeed hell cut a seed) x i ≠
        reductionAssignment hell seed x i) :
    Encoding.rowOfBit ell i = cut.lower ∨
      Encoding.rowOfBit ell i = cut.upper := by
  by_contra hrows
  rw [not_or] at hrows
  exact hchange
    (reductionAssignment_reroute_eq_of_row_ne hell cut a seed i hrows.1 hrows.2)

theorem rerouteSeed_involutive
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    rerouteSeed hell cut a (rerouteSeed hell cut a seed) = seed := by
  funext j
  by_cases hrow : cut.upper.val ≤ (labelOfBit hell j).val
  · simp only [rerouteSeed_apply_of_upper_le hell cut a _ j hrow]
    apply Equiv.ext
    intro c
    simp
  · have hlt : (labelOfBit hell j).val < cut.upper.val := Nat.lt_of_not_ge hrow
    simp [rerouteSeed_apply_of_lt_upper hell cut a _ j hlt]

/-- Rerouting by fixed cut and active label is a seed-space involution. -/
noncomputable def rerouteSeedEquiv
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x)) :
    RowPermSeed (BinaryPointer.order ell) ≃
      RowPermSeed (BinaryPointer.order ell) where
  toFun := rerouteSeed hell cut a
  invFun := rerouteSeed hell cut a
  left_inv := rerouteSeed_involutive hell cut a
  right_inv := rerouteSeed_involutive hell cut a

@[simp]
theorem rerouteSeedEquiv_apply
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    rerouteSeedEquiv hell cut a seed = rerouteSeed hell cut a seed :=
  rfl

end ApproxNS

end SoPL

end Revres
