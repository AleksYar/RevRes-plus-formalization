import Revres.DecisionTree.Polynomial
import Revres.SoPL.ApproxNS.Reduction

/-!
# Polynomial substitution for the OR-to-SoPL reduction

For a fixed row-permutation seed, every encoded bit of the deterministic reduction is either
constant or queries one OR coordinate. The resulting depth-one decision trees give an exact
degree-preserving substitution from SoPL polynomials to OR polynomials.
-/

namespace Revres

open Lemma53

namespace SoPL

namespace ApproxNS

/-- The successor stored at `u` when its fixed path label is active. -/
noncomputable def activeSuccessorPointer {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell) : Option (Fin (BinaryPointer.order ell)) :=
  let c := nodeLabel hell seed u
  if hu : u.IsInternal then
    some (pathOf hell seed c ⟨u.row.val + 1, hu⟩)
  else
    some u.column

/-- The predecessor stored at `u` when its fixed path label is active. -/
noncomputable def activePredecessorPointer {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell) : Option (Fin (BinaryPointer.order ell)) :=
  let c := nodeLabel hell seed u
  match labelCase hell u.row with
  | none => none
  | some j => some (pathOf hell seed c (previousRow hell j))

theorem reductionInput_successor_eq_ite {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (u : Encoding.Node ell) :
    (reductionInput hell seed x).successor u =
      if labelActive hell x (nodeLabel hell seed u) then
        activeSuccessorPointer hell seed u
      else
        none := by
  rfl

theorem reductionInput_predecessor_eq_ite {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (x : ORInput ell)
    (u : Encoding.Node ell) :
    (reductionInput hell seed x).predecessor u =
      if labelActive hell x (nodeLabel hell seed u) then
        activePredecessorPointer hell seed u
      else
        none := by
  rfl

/-- The fixed active pointer selected by an encoded successor/predecessor tag. -/
noncomputable def activePointer {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (u : Encoding.Node ell) (kind : Fin 2) :
    Option (Fin (BinaryPointer.order ell)) :=
  if kind = 0 then
    activeSuccessorPointer hell seed u
  else
    activePredecessorPointer hell seed u

/-- The decision tree computing one encoded bit of the fixed-seed reduction. -/
noncomputable def reductionBitTree {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (i : Fin (Encoding.variableCount ell)) :
    DecisionTree (BinaryPointer.order ell - 1) F2 :=
  let index := (Encoding.bitIndexEquiv ell).symm i
  let inactiveBit := BinaryPointer.encode none index.2.2
  let activeBit := BinaryPointer.encode
    (activePointer hell seed index.1 index.2.1) index.2.2
  match labelCase hell (nodeLabel hell seed index.1) with
  | none => .leaf activeBit
  | some j => .query j (.leaf inactiveBit) (.leaf activeBit)

private theorem encodeInput_reduction_eq_ite {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (i : Fin (Encoding.variableCount ell)) (x : ORInput ell) :
    let index := (Encoding.bitIndexEquiv ell).symm i
    Encoding.encodeInput ell (reductionInput hell seed x) i =
      if labelActive hell x (nodeLabel hell seed index.1) then
        BinaryPointer.encode
          (activePointer hell seed index.1 index.2.1) index.2.2
      else
        BinaryPointer.encode none index.2.2 := by
  dsimp only
  by_cases hkind : ((Encoding.bitIndexEquiv ell).symm i).2.1 = 0
  · rw [Encoding.encodeInput]
    simp only [hkind, if_pos]
    rw [reductionInput_successor_eq_ite]
    by_cases hactive :
        labelActive hell x (nodeLabel hell seed ((Encoding.bitIndexEquiv ell).symm i).1)
    · simp [hactive, activePointer]
    · simp [hactive]
  · rw [Encoding.encodeInput]
    simp only [hkind]
    rw [reductionInput_predecessor_eq_ite]
    by_cases hactive :
        labelActive hell x (nodeLabel hell seed ((Encoding.bitIndexEquiv ell).symm i).1)
    · simp [hactive, activePointer, hkind]
    · simp [hactive]

@[simp]
theorem eval_reductionBitTree {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (i : Fin (Encoding.variableCount ell)) (x : ORInput ell) :
    (reductionBitTree hell seed i).eval x =
      Encoding.encodeInput ell (reductionInput hell seed x) i := by
  let index := (Encoding.bitIndexEquiv ell).symm i
  rw [encodeInput_reduction_eq_ite]
  cases hlabel : labelCase hell (nodeLabel hell seed index.1) with
  | none =>
      simp [reductionBitTree, index, hlabel, labelActive]
  | some j =>
      rcases F2_eq_zero_or_one (x j) with hj | hj
      · simp [reductionBitTree, index, hlabel, labelActive, hj]
      · simp [reductionBitTree, index, hlabel, labelActive, hj]

theorem depth_reductionBitTree_le_one {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (i : Fin (Encoding.variableCount ell)) :
    (reductionBitTree hell seed i).depth ≤ 1 := by
  dsimp only [reductionBitTree]
  cases hlabel :
      labelCase hell (nodeLabel hell seed ((Encoding.bitIndexEquiv ell).symm i).1) <;>
    simp

/-- Substitute every encoded SoPL variable by its fixed-seed reduction bit tree. -/
noncomputable def reductionSubstitution {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    BooleanPolynomial (Encoding.variableCount ell) →ₐ[ℝ]
      BooleanPolynomial (BinaryPointer.order ell - 1) :=
  DecisionTree.substituteTrees (reductionBitTree hell seed)

@[simp]
theorem reductionSubstitution_C {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) (r : ℝ) :
    reductionSubstitution hell seed (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [reductionSubstitution]

@[simp]
theorem reductionSubstitution_X {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (i : Fin (Encoding.variableCount ell)) :
    reductionSubstitution hell seed (MvPolynomial.X i) =
      (reductionBitTree hell seed i).polynomial f2ToReal := by
  simp [reductionSubstitution]

theorem evalBoolean_reductionSubstitution {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (p : BooleanPolynomial (Encoding.variableCount ell))
    (x : ORInput ell) :
    evalBoolean x (reductionSubstitution hell seed p) =
      evalBoolean
        (Encoding.encodeInput ell (reductionInput hell seed x)) p := by
  rw [reductionSubstitution, DecisionTree.evalBoolean_substituteTrees]
  apply congrArg
    (fun y : Fin (Encoding.variableCount ell) → F2 ↦ evalBoolean y p)
  funext i
  exact eval_reductionBitTree hell seed i x

theorem totalDegree_reductionSubstitution_le {ell : ℕ} (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (p : BooleanPolynomial (Encoding.variableCount ell)) :
    (reductionSubstitution hell seed p).totalDegree ≤ p.totalDegree := by
  simpa [reductionSubstitution] using
    (DecisionTree.totalDegree_substituteTrees_le
      (d := 1) (reductionBitTree hell seed)
      (depth_reductionBitTree_le_one hell seed) p)

theorem totalDegree_reductionSubstitution_le_of_le {ell k : ℕ}
    (hell : 0 < ell)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (p : BooleanPolynomial (Encoding.variableCount ell))
    (hp : p.totalDegree ≤ k) :
    (reductionSubstitution hell seed p).totalDegree ≤ k :=
  (totalDegree_reductionSubstitution_le hell seed p).trans hp

end ApproxNS

end SoPL

end Revres
