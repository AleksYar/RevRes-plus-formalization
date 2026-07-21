import Revres.Grid.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Macrogrid geometry for Sink-of-DAG

An `(n * n)`-by-`(n * n)` ambient grid is partitioned into an `n`-by-`n` grid of
`n`-by-`n` boxes. The last box in each macro-row is reserved for parking; the other boxes are
candidates for the later amplification construction.
-/

namespace Revres

namespace SoD

variable {n : ℕ}

/-- Embed a local node `u` into the macro-box indexed by `Q`. -/
def macroEmbed (Q u : GridNode n) : GridNode (n * n) :=
  ((finProdFinEquiv (m := n) (n := n)) (Q.row, u.row),
    (finProdFinEquiv (m := n) (n := n)) (Q.column, u.column))

/-- The unique macro-box containing an ambient node. -/
def macroIndex (v : GridNode (n * n)) : GridNode n :=
  (((finProdFinEquiv (m := n) (n := n)).symm v.row).1,
    ((finProdFinEquiv (m := n) (n := n)).symm v.column).1)

/-- The local coordinates of an ambient node inside its macro-box. -/
def localNode (v : GridNode (n * n)) : GridNode n :=
  (((finProdFinEquiv (m := n) (n := n)).symm v.row).2,
    ((finProdFinEquiv (m := n) (n := n)).symm v.column).2)

@[simp]
theorem macroIndex_macroEmbed (Q u : GridNode n) :
    macroIndex (macroEmbed Q u) = Q := by
  apply Prod.ext <;> simp [macroIndex, macroEmbed]

@[simp]
theorem localNode_macroEmbed (Q u : GridNode n) :
    localNode (macroEmbed Q u) = u := by
  apply Prod.ext <;> simp [localNode, macroEmbed]

@[simp]
theorem macroEmbed_macroIndex_localNode (v : GridNode (n * n)) :
    macroEmbed (macroIndex v) (localNode v) = v := by
  apply Prod.ext
  · change (finProdFinEquiv (m := n) (n := n))
      ((finProdFinEquiv (m := n) (n := n)).symm v.row) = v.row
    exact (finProdFinEquiv (m := n) (n := n)).apply_symm_apply v.row
  · change (finProdFinEquiv (m := n) (n := n))
      ((finProdFinEquiv (m := n) (n := n)).symm v.column) = v.column
    exact (finProdFinEquiv (m := n) (n := n)).apply_symm_apply v.column

theorem macroEmbed_right_injective (Q : GridNode n) :
    Function.Injective (macroEmbed Q) := by
  intro u v huv
  have hlocal := congrArg localNode huv
  simpa using hlocal

/-- The finite set of ambient nodes in one macro-box. -/
def macroSubgrid (Q : GridNode n) : Finset (GridNode (n * n)) :=
  Finset.univ.image (macroEmbed Q)

theorem mem_macroSubgrid_iff {Q : GridNode n} {v : GridNode (n * n)} :
    v ∈ macroSubgrid Q ↔ macroIndex v = Q := by
  constructor
  · rw [macroSubgrid, Finset.mem_image]
    rintro ⟨u, _hu, rfl⟩
    exact macroIndex_macroEmbed Q u
  · intro hindex
    rw [macroSubgrid, Finset.mem_image]
    refine ⟨localNode v, Finset.mem_univ _, ?_⟩
    rw [← hindex]
    exact macroEmbed_macroIndex_localNode v

/-- Distinct macro-boxes contain no common ambient node. -/
theorem macroSubgrid_disjoint {Q R : GridNode n} (hQR : Q ≠ R) :
    Disjoint (macroSubgrid Q) (macroSubgrid R) := by
  rw [Finset.disjoint_left]
  intro v hvQ hvR
  exact hQR ((mem_macroSubgrid_iff.mp hvQ).symm.trans (mem_macroSubgrid_iff.mp hvR))

theorem card_macroSubgrid (Q : GridNode n) :
    (macroSubgrid Q).card = n * n := by
  rw [macroSubgrid, Finset.card_image_of_injective _ (macroEmbed_right_injective Q)]
  simp

/-- Every ambient node belongs to exactly one macro-box. -/
theorem existsUnique_mem_macroSubgrid (v : GridNode (n * n)) :
    ∃! Q : GridNode n, v ∈ macroSubgrid Q := by
  refine ⟨macroIndex v, mem_macroSubgrid_iff.mpr rfl, ?_⟩
  intro Q hQ
  exact (mem_macroSubgrid_iff.mp hQ).symm

/-- The top-left corner of a macro-box. -/
def subgridCorner (hn : 0 < n) (Q : GridNode n) : GridNode (n * n) :=
  macroEmbed Q (GridNode.distinguished hn)

theorem subgridCorner_mem (hn : 0 < n) (Q : GridNode n) :
    subgridCorner hn Q ∈ macroSubgrid Q := by
  exact mem_macroSubgrid_iff.mpr (macroIndex_macroEmbed Q (GridNode.distinguished hn))

@[simp]
theorem subgridCorner_row_val (hn : 0 < n) (Q : GridNode n) :
    (subgridCorner hn Q).row.val = n * Q.row.val := by
  simp [subgridCorner, macroEmbed, GridNode.distinguished, finProdFinEquiv]

@[simp]
theorem subgridCorner_column_val (hn : 0 < n) (Q : GridNode n) :
    (subgridCorner hn Q).column.val = n * Q.column.val := by
  simp [subgridCorner, macroEmbed, GridNode.distinguished, finProdFinEquiv]

/-- The first macro-box corner is the distinguished ambient source. -/
theorem distinguished_subgridCorner (hn : 0 < n) :
    subgridCorner hn (GridNode.distinguished hn) =
      GridNode.distinguished (Nat.mul_pos hn hn) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [subgridCorner, macroEmbed, GridNode.distinguished, finProdFinEquiv]

/-- The last column of the macrogrid, reserved for parking. -/
def parkingColumn (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩

/-- The parking box in macro-row `i`. -/
def parkingBox (hn : 0 < n) (i : Fin n) : GridNode n :=
  (i, parkingColumn hn)

/-- The top-left corner of the parking box in macro-row `i`. -/
def parkingCorner (hn : 0 < n) (i : Fin n) : GridNode (n * n) :=
  subgridCorner hn (parkingBox hn i)

/-- All macro-boxes in row `i`. -/
def macroRow (i : Fin n) : Finset (GridNode n) :=
  Finset.univ.image fun j : Fin n => (i, j)

theorem mem_macroRow_iff {i : Fin n} {Q : GridNode n} :
    Q ∈ macroRow i ↔ Q.row = i := by
  constructor
  · rw [macroRow, Finset.mem_image]
    rintro ⟨j, _hj, rfl⟩
    rfl
  · intro hrow
    rw [macroRow, Finset.mem_image]
    refine ⟨Q.column, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact hrow.symm
    · rfl

theorem card_macroRow (i : Fin n) :
    (macroRow i).card = n := by
  rw [macroRow, Finset.card_image_of_injective _ (Prod.mk_right_injective i)]
  simp

/-- The nonparking boxes in macro-row `i`. -/
def candidateBoxes (hn : 0 < n) (i : Fin n) : Finset (GridNode n) :=
  (Finset.univ.erase (parkingColumn hn)).image fun j : Fin n => (i, j)

theorem mem_candidateBoxes_iff
    {hn : 0 < n} {i : Fin n} {Q : GridNode n} :
    Q ∈ candidateBoxes hn i ↔
      Q.row = i ∧ Q.column ≠ parkingColumn hn := by
  constructor
  · rw [candidateBoxes, Finset.mem_image]
    rintro ⟨j, hj, rfl⟩
    exact ⟨rfl, (Finset.mem_erase.mp hj).1⟩
  · rintro ⟨hrow, hcolumn⟩
    rw [candidateBoxes, Finset.mem_image]
    refine ⟨Q.column, Finset.mem_erase.mpr ⟨hcolumn, Finset.mem_univ _⟩, ?_⟩
    apply Prod.ext
    · exact hrow.symm
    · rfl

theorem parkingBox_not_mem_candidateBoxes (hn : 0 < n) (i : Fin n) :
    parkingBox hn i ∉ candidateBoxes hn i := by
  rw [mem_candidateBoxes_iff]
  simp [parkingBox]

theorem card_candidateBoxes (hn : 0 < n) (i : Fin n) :
    (candidateBoxes hn i).card = n - 1 := by
  rw [candidateBoxes, Finset.card_image_of_injective _ (Prod.mk_right_injective i)]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (parkingColumn hn))]
  simp

/-- Candidate boxes one macro-row below `Q`. -/
def nextMacroRowCandidates (hn : 0 < n) (Q : GridNode n) : Finset (GridNode n) :=
  Finset.univ.filter fun R => Q.NextRow R ∧ R.column ≠ parkingColumn hn

theorem mem_nextMacroRowCandidates_iff
    {hn : 0 < n} {Q R : GridNode n} :
    R ∈ nextMacroRowCandidates hn Q ↔
      Q.NextRow R ∧ R.column ≠ parkingColumn hn := by
  simp [nextMacroRowCandidates]

/-- The index of the macro-row immediately below an internal macro-box. -/
def nextMacroRowIndex (Q : GridNode n) (hQ : Q.IsInternal) : Fin n :=
  ⟨Q.row.val + 1, hQ⟩

theorem nextMacroRowCandidates_eq_candidateBoxes
    (hn : 0 < n) (Q : GridNode n) (hQ : Q.IsInternal) :
    nextMacroRowCandidates hn Q = candidateBoxes hn (nextMacroRowIndex Q hQ) := by
  ext R
  rw [mem_nextMacroRowCandidates_iff, mem_candidateBoxes_iff]
  constructor
  · rintro ⟨hnext, hcolumn⟩
    refine ⟨Fin.ext ?_, hcolumn⟩
    exact hnext
  · rintro ⟨hrow, hcolumn⟩
    refine ⟨?_, hcolumn⟩
    exact congrArg Fin.val hrow

theorem nextMacroRowCandidates_card
    (hn : 0 < n) (Q : GridNode n) (hQ : Q.IsInternal) :
    (nextMacroRowCandidates hn Q).card = n - 1 := by
  rw [nextMacroRowCandidates_eq_candidateBoxes hn Q hQ]
  exact card_candidateBoxes hn (nextMacroRowIndex Q hQ)

theorem nextMacroRowCandidates_eq_empty
    (hn : 0 < n) {Q : GridNode n} (hQ : Q.IsLastRow) :
    nextMacroRowCandidates hn Q = ∅ := by
  ext R
  constructor
  · intro hR
    have hnext := (mem_nextMacroRowCandidates_iff.mp hR).1
    exact (GridNode.not_internal_of_last hQ (GridNode.nextRow_internal hnext)).elim
  · intro hR
    simp at hR

theorem nextCandidate_nextRow
    {hn : 0 < n} {Q R : GridNode n}
    (hR : R ∈ nextMacroRowCandidates hn Q) :
    Q.NextRow R :=
  (mem_nextMacroRowCandidates_iff.mp hR).1

/-- Corners in consecutive macro-rows are exactly `n` ambient rows apart. -/
theorem subgridCorner_row_step
    (hn : 0 < n) {Q R : GridNode n} (hQR : Q.NextRow R) :
    (subgridCorner hn R).row.val =
      (subgridCorner hn Q).row.val + n := by
  rw [subgridCorner_row_val, subgridCorner_row_val, hQR, Nat.mul_add, Nat.mul_one]

theorem nextCandidate_subgrids_disjoint
    {hn : 0 < n} {Q R S : GridNode n}
    (_hR : R ∈ nextMacroRowCandidates hn Q)
    (_hS : S ∈ nextMacroRowCandidates hn Q) (hRS : R ≠ S) :
    Disjoint (macroSubgrid R) (macroSubgrid S) :=
  macroSubgrid_disjoint hRS

end SoD

end Revres
