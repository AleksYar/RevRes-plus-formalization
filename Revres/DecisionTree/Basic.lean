import Revres.Conical.Term
import Mathlib.Data.Fintype.OfMap

/-!
# Generic Boolean decision trees

Decision trees query `F2` coordinates, taking the zero child first and the one child second. Leaf
paths are occurrence-sensitive. Their canonical partial assignments are absent exactly when
repeated queries make the path contradictory.
-/

namespace Revres

open Lemma53

universe u

/-- A Boolean decision tree with values of type `α` at its leaves. -/
inductive DecisionTree (N : ℕ) (α : Type u) : Type u where
  | leaf : α → DecisionTree N α
  | query : Fin N → DecisionTree N α → DecisionTree N α → DecisionTree N α

namespace DecisionTree

variable {N : ℕ} {α : Type u}

/-- Evaluate a decision tree, taking the zero child first and the one child second. -/
def eval : DecisionTree N α → (Fin N → F2) → α
  | .leaf a, _ => a
  | .query i zeroTree oneTree, x =>
      if x i = 0 then zeroTree.eval x else oneTree.eval x

@[simp]
theorem eval_leaf (a : α) (x : Fin N → F2) :
    (leaf a : DecisionTree N α).eval x = a :=
  rfl

@[simp]
theorem eval_query_zero {i : Fin N} {zeroTree oneTree : DecisionTree N α}
    {x : Fin N → F2} (hi : x i = 0) :
    (query i zeroTree oneTree).eval x = zeroTree.eval x := by
  simp [eval, hi]

@[simp]
theorem eval_query_one {i : Fin N} {zeroTree oneTree : DecisionTree N α}
    {x : Fin N → F2} (hi : x i = 1) :
    (query i zeroTree oneTree).eval x = oneTree.eval x := by
  simp [eval, hi]

/-- Exact worst-case query depth. -/
@[simp]
def depth : DecisionTree N α → ℕ
  | .leaf _ => 0
  | .query _ zeroTree oneTree => 1 + max zeroTree.depth oneTree.depth

theorem depth_zero_le_query (i : Fin N) (zeroTree oneTree : DecisionTree N α) :
    zeroTree.depth + 1 ≤ (query i zeroTree oneTree).depth := by
  simp only [depth]
  rw [Nat.add_comm 1 (max zeroTree.depth oneTree.depth)]
  exact Nat.add_le_add_right (Nat.le_max_left _ _) 1

theorem depth_one_le_query (i : Fin N) (zeroTree oneTree : DecisionTree N α) :
    oneTree.depth + 1 ≤ (query i zeroTree oneTree).depth := by
  simp only [depth]
  rw [Nat.add_comm 1 (max zeroTree.depth oneTree.depth)]
  exact Nat.add_le_add_right (Nat.le_max_right _ _) 1

/-- A root-to-leaf path, retaining the identity of the leaf occurrence. -/
inductive LeafPath : DecisionTree N α → Type u
  | leaf (a : α) : LeafPath (.leaf a)
  | zero {i : Fin N} {zeroTree oneTree : DecisionTree N α} :
      LeafPath zeroTree → LeafPath (.query i zeroTree oneTree)
  | one {i : Fin N} {zeroTree oneTree : DecisionTree N α} :
      LeafPath oneTree → LeafPath (.query i zeroTree oneTree)

namespace LeafPath

/-- The value stored at a leaf occurrence. -/
@[simp]
def value : {T : DecisionTree N α} → T.LeafPath → α
  | .leaf _, .leaf a => a
  | .query _ _ _, .zero path => path.value
  | .query _ _ _, .one path => path.value

/-- The number of queries on a root-to-leaf path. -/
@[simp]
def length : {T : DecisionTree N α} → T.LeafPath → ℕ
  | .leaf _, .leaf _ => 0
  | .query _ _ _, .zero path => 1 + path.length
  | .query _ _ _, .one path => 1 + path.length

/-- The variables queried on a root-to-leaf path, with repeated queries merged. -/
@[simp]
def queriedVars : {T : DecisionTree N α} → T.LeafPath → Finset (Fin N)
  | .leaf _, .leaf _ => ∅
  | .query i _ _, .zero path => insert i path.queriedVars
  | .query i _ _, .one path => insert i path.queriedVars

/-- An assignment follows every branch on this root-to-leaf path. -/
@[simp]
def Matches : {T : DecisionTree N α} → T.LeafPath → (Fin N → F2) → Prop
  | .leaf _, .leaf _, _ => True
  | .query i _ _, .zero path, x => x i = 0 ∧ path.Matches x
  | .query i _ _, .one path, x => x i = 1 ∧ path.Matches x

theorem length_le_depth {T : DecisionTree N α} (path : T.LeafPath) :
    path.length ≤ T.depth := by
  induction path with
  | leaf => simp
  | @zero i zeroTree oneTree path ih =>
      exact Nat.add_le_add_left (ih.trans (Nat.le_max_left _ _)) 1
  | @one i zeroTree oneTree path ih =>
      exact Nat.add_le_add_left (ih.trans (Nat.le_max_right _ _)) 1

theorem matches_agree_on_variables {T : DecisionTree N α} (path : T.LeafPath)
    {x y : Fin N → F2} (hx : path.Matches x) (hy : path.Matches y) :
    ∀ i ∈ path.queriedVars, x i = y i := by
  induction path with
  | leaf => simp
  | @zero i zeroTree oneTree path ih =>
      intro j hj
      rw [queriedVars, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hx.1.trans hy.1.symm
      · exact ih hx.2 hy.2 j hj
  | @one i zeroTree oneTree path ih =>
      intro j hj
      rw [queriedVars, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hx.1.trans hy.1.symm
      · exact ih hx.2 hy.2 j hj

theorem matches_of_agrees_on_variables {T : DecisionTree N α} (path : T.LeafPath)
    {x y : Fin N → F2} (hy : path.Matches y)
    (hxy : ∀ i ∈ path.queriedVars, x i = y i) :
    path.Matches x := by
  induction path with
  | leaf => trivial
  | @zero i zeroTree oneTree path ih =>
      constructor
      · exact (hxy i (by simp)).trans hy.1
      · apply ih hy.2
        intro j hj
        exact hxy j (by simp [hj])
  | @one i zeroTree oneTree path ih =>
      constructor
      · exact (hxy i (by simp)).trans hy.1
      · apply ih hy.2
        intro j hj
        exact hxy j (by simp [hj])

end LeafPath

/-- Enumerate every leaf occurrence of a tree. -/
def allLeafPaths : (T : DecisionTree N α) → List T.LeafPath
  | .leaf a => [.leaf a]
  | .query i zeroTree oneTree =>
      (allLeafPaths zeroTree).map
          (fun path => LeafPath.zero (i := i) (oneTree := oneTree) path) ++
        (allLeafPaths oneTree).map
          (fun path => LeafPath.one (i := i) (zeroTree := zeroTree) path)

theorem LeafPath.mem_allLeafPaths {T : DecisionTree N α} (path : T.LeafPath) :
    path ∈ T.allLeafPaths := by
  induction path <;> simp_all [allLeafPaths]

noncomputable instance leafPathDecidableEq (T : DecisionTree N α) :
    DecidableEq T.LeafPath :=
  Classical.decEq _

noncomputable instance leafPathFintype (T : DecisionTree N α) : Fintype T.LeafPath := by
  classical
  exact Fintype.ofList T.allLeafPaths fun path => path.mem_allLeafPaths

/-- The leaf occurrence reached by an assignment. -/
def reachedLeaf : (T : DecisionTree N α) → (x : Fin N → F2) → T.LeafPath
  | .leaf a, _ => .leaf a
  | .query i zeroTree oneTree, x =>
      if x i = 0 then .zero (reachedLeaf zeroTree x) else .one (reachedLeaf oneTree x)

@[simp]
theorem reachedLeaf_matches (T : DecisionTree N α) (x : Fin N → F2) :
    (T.reachedLeaf x).Matches x := by
  induction T with
  | leaf => simp [reachedLeaf]
  | query i zeroTree oneTree ihzero ihone =>
      rcases F2_eq_zero_or_one (x i) with hi | hi
      · simp [reachedLeaf, hi, ihzero]
      · simp [reachedLeaf, hi, ihone]

theorem LeafPath.eq_reachedLeaf_of_matches {T : DecisionTree N α}
    (path : T.LeafPath) {x : Fin N → F2} (h : path.Matches x) :
    path = T.reachedLeaf x := by
  induction path with
  | leaf => rfl
  | @zero i zeroTree oneTree path ih =>
      simp only [LeafPath.Matches] at h
      simp [reachedLeaf, h.1, ih h.2]
  | @one i zeroTree oneTree path ih =>
      simp only [LeafPath.Matches] at h
      simp [reachedLeaf, h.1, ih h.2]

theorem existsUnique_leafPath_matches
    (T : DecisionTree N α) (x : Fin N → F2) :
    ∃! path : T.LeafPath, path.Matches x :=
  ⟨T.reachedLeaf x, T.reachedLeaf_matches x,
    fun path hpath => path.eq_reachedLeaf_of_matches hpath⟩

theorem eval_eq_leafValue_of_matches {T : DecisionTree N α}
    (path : T.LeafPath) {x : Fin N → F2} (h : path.Matches x) :
    T.eval x = path.value := by
  induction path with
  | leaf => rfl
  | @zero i zeroTree oneTree path ih =>
      simp only [LeafPath.Matches] at h
      rw [eval_query_zero h.1]
      simpa using ih h.2
  | @one i zeroTree oneTree path ih =>
      simp only [LeafPath.Matches] at h
      rw [eval_query_one h.1]
      simpa using ih h.2

namespace Term

theorem matches_ofCube_iff (U : Finset (Fin N)) (assignment x : Fin N → F2) :
    (Term.ofCube U assignment).Matches x ↔
      ∀ i ∈ U, x i = assignment i := by
  constructor
  · intro hmatch i hi
    exact hmatch i (assignment i) (by simp [Term.ofCube, hi])
  · intro hagree i b hib
    by_cases hi : i ∈ U
    · have hab : assignment i = b := by
        simpa [Term.ofCube, hi] using hib
      exact (hagree i hi).trans hab
    · simp [Term.ofCube, hi] at hib

end Term

/-- The canonical term of a reachable leaf, or `none` for a contradictory path. -/
noncomputable def leafPartialAssignment {T : DecisionTree N α}
    (path : T.LeafPath) : Option (Term N) := by
  classical
  exact if h : ∃ x, path.Matches x then
      some (Term.ofCube path.queriedVars (Classical.choose h))
    else
      none

theorem LeafPath.matches_iff_of_leafPartialAssignment_eq_some
    {T : DecisionTree N α} (path : T.LeafPath) {term : Term N}
    (hterm : leafPartialAssignment path = some term) (x : Fin N → F2) :
    path.Matches x ↔ term.Matches x := by
  classical
  unfold leafPartialAssignment at hterm
  split at hterm
  next hreachable =>
    simp only [Option.some.injEq] at hterm
    subst term
    rw [Term.matches_ofCube_iff]
    constructor
    · intro hx i hi
      exact path.matches_agree_on_variables hx (Classical.choose_spec hreachable) i hi
    · intro hagree
      exact path.matches_of_agrees_on_variables (Classical.choose_spec hreachable) hagree
  next hunreachable =>
    simp at hterm

theorem LeafPath.leafPartialAssignment_ne_none_of_matches
    {T : DecisionTree N α} (path : T.LeafPath) {x : Fin N → F2}
    (h : path.Matches x) :
    leafPartialAssignment path ≠ none := by
  classical
  unfold leafPartialAssignment
  rw [dif_pos ⟨x, h⟩]
  simp

theorem LeafPath.not_matches_of_leafPartialAssignment_eq_none
    {T : DecisionTree N α} (path : T.LeafPath)
    (hterm : leafPartialAssignment path = none) (x : Fin N → F2) :
    ¬path.Matches x := by
  intro hmatch
  exact path.leafPartialAssignment_ne_none_of_matches hmatch hterm

theorem LeafPath.support_of_leafPartialAssignment_eq_some
    {T : DecisionTree N α} (path : T.LeafPath) {term : Term N}
    (hterm : leafPartialAssignment path = some term) :
    term.support = path.queriedVars := by
  classical
  unfold leafPartialAssignment at hterm
  split at hterm
  next hreachable =>
    simp only [Option.some.injEq] at hterm
    subst term
    exact Term.support_ofCube _ _
  next hunreachable =>
    simp at hterm

theorem existsUnique_leafCube_matches
    (T : DecisionTree N α) (x : Fin N → F2) :
    ∃! path : T.LeafPath,
      ∃ term : Term N,
        leafPartialAssignment path = some term ∧ term.Matches x := by
  obtain ⟨path, hmatch, hunique⟩ := T.existsUnique_leafPath_matches x
  have hsome := path.leafPartialAssignment_ne_none_of_matches hmatch
  cases hterm : leafPartialAssignment path with
  | none => exact False.elim (hsome hterm)
  | some term =>
      refine ⟨path, ⟨term, hterm, ?_⟩, ?_⟩
      · exact (path.matches_iff_of_leafPartialAssignment_eq_some hterm x).mp hmatch
      · intro other hother
        obtain ⟨otherTerm, hotherTerm, hotherMatches⟩ := hother
        apply hunique other
        exact (other.matches_iff_of_leafPartialAssignment_eq_some
          hotherTerm x).mpr hotherMatches

end DecisionTree

end Revres
