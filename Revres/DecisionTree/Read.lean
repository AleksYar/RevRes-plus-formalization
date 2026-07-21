import Revres.DecisionTree.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Decision-tree read combinators

Mapping and binding preserve the existing zero-child/one-child convention. Fixed tuples are read
in increasing `Fin` order, without requiring the queried coordinates to be distinct.
-/

namespace Revres

open Lemma53

namespace DecisionTree

universe u v

variable {N k : ℕ} {α : Type u} {β : Type v}

/-- Map every leaf value of a decision tree. -/
def map (f : α → β) : DecisionTree N α → DecisionTree N β
  | .leaf a => .leaf (f a)
  | .query i zeroTree oneTree =>
      .query i (zeroTree.map f) (oneTree.map f)

@[simp]
theorem eval_map (T : DecisionTree N α) (f : α → β) (x : Fin N → F2) :
    (T.map f).eval x = f (T.eval x) := by
  induction T with
  | leaf => rfl
  | query i zeroTree oneTree ihzero ihone =>
      simp only [map, eval]
      split <;> simp_all

@[simp]
theorem depth_map (T : DecisionTree N α) (f : α → β) :
    (T.map f).depth = T.depth := by
  induction T with
  | leaf => rfl
  | query i zeroTree oneTree ihzero ihone =>
      simp [map, ihzero, ihone]

/-- Replace each leaf by a continuation tree over the same input coordinates. -/
def bind (T : DecisionTree N α) (next : α → DecisionTree N β) : DecisionTree N β :=
  match T with
  | .leaf a => next a
  | .query i zeroTree oneTree =>
      .query i (zeroTree.bind next) (oneTree.bind next)

@[simp]
theorem eval_bind (T : DecisionTree N α) (next : α → DecisionTree N β)
    (x : Fin N → F2) :
    (T.bind next).eval x = (next (T.eval x)).eval x := by
  induction T with
  | leaf => rfl
  | query i zeroTree oneTree ihzero ihone =>
      simp only [bind, eval]
      split <;> simp_all

theorem depth_bind_le (T : DecisionTree N α) (next : α → DecisionTree N β) {d : ℕ}
    (hnext : ∀ a, (next a).depth ≤ d) :
    (T.bind next).depth ≤ T.depth + d := by
  induction T with
  | leaf a => simpa [bind] using hnext a
  | query i zeroTree oneTree ihzero ihone =>
      simp only [bind, depth]
      calc
        1 + max (zeroTree.bind next).depth (oneTree.bind next).depth ≤
            1 + max (zeroTree.depth + d) (oneTree.depth + d) :=
          Nat.add_le_add_left (max_le_max ihzero ihone) 1
        _ = 1 + max zeroTree.depth oneTree.depth + d := by
          simp [max_add_add_right, Nat.add_assoc]

/-- Read a fixed tuple of coordinates in increasing `Fin` order. -/
def readTuple : {k : ℕ} → (Fin k → Fin N) → DecisionTree N (Fin k → F2)
  | 0, _ => .leaf Fin.elim0
  | k + 1, index =>
      .query (index 0)
        ((readTuple (fun i : Fin k => index i.succ)).map (Fin.cons 0))
        ((readTuple (fun i : Fin k => index i.succ)).map (Fin.cons 1))

@[simp]
theorem eval_readTuple (index : Fin k → Fin N) (x : Fin N → F2) :
    (readTuple index).eval x = fun i => x (index i) := by
  induction k with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ k ih =>
      rcases F2_eq_zero_or_one (x (index 0)) with hzero | hone
      · rw [readTuple, eval_query_zero hzero, eval_map, ih]
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [hzero]
        · simp
      · rw [readTuple, eval_query_one hone, eval_map, ih]
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [hone]
        · simp

@[simp]
theorem depth_readTuple (index : Fin k → Fin N) :
    (readTuple index).depth = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [readTuple, ih, Nat.add_comm]

end DecisionTree

end Revres
