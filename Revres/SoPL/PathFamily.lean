import Revres.SoPL.Semantics
import Mathlib.Data.Set.Finite.Basic

/-!
# Structured SoPL path inputs

The path family is described by an explicit finite collection of complete paths. Its active graph
is exactly the union of their consecutive edges, and its active last-row nodes are exactly their
endpoints.
-/

namespace Revres

namespace SoPL

/-- A complete grid path, represented by its column in every row. -/
abbrev Path (n : ℕ) := Fin n → Fin n

namespace Path

variable {n : ℕ}

/-- A path contains a node when it selects the node's column in that row. -/
def Contains (p : Path n) (u : GridNode n) : Prop :=
  p u.row = u.column

instance containsDecidable (p : Path n) (u : GridNode n) :
    Decidable (p.Contains u) :=
  inferInstanceAs (Decidable (p u.row = u.column))

/-- A consecutive grid edge lies on a path. -/
def Edge (p : Path n) (u v : GridNode n) : Prop :=
  u.NextRow v ∧ p.Contains u ∧ p.Contains v

instance edgeDecidable (p : Path n) (u v : GridNode n) :
    Decidable (p.Edge u v) := by
  unfold Edge
  infer_instance

end Path

/-- An explicit decomposition of a semantic SoPL input into disjoint complete paths. -/
structure PathFamilyWitness {n : ℕ} (hn : 0 < n) (x : Input n) where
  paths : Finset (Path n)
  pairwiseDisjoint :
    ∀ p, p ∈ paths → ∀ q, q ∈ paths → p ≠ q →
      ∀ r, p r ≠ q r
  activeEdge_iff :
    ∀ u v, x.ActiveEdge u v ↔
      ∃ p ∈ paths, p.Edge u v
  activeLast_iff :
    ∀ u, u.IsLastRow →
      (x.Active u ↔ ∃ p ∈ paths, p.Contains u)
  distinguished :
    ∃ p ∈ paths,
      p ⟨0, hn⟩ = ⟨0, hn⟩

/-- Membership in the semantic path family. -/
def IsPathFamily {n : ℕ} (hn : 0 < n) (x : Input n) : Prop :=
  Nonempty (PathFamilyWitness hn x)

/-- The set of semantic SoPL inputs admitting a path-family decomposition. -/
def pathFamily (n : ℕ) (hn : 0 < n) : Set (Input n) :=
  {x | IsPathFamily hn x}

namespace PathFamilyWitness

variable {n : ℕ} {hn : 0 < n} {x : Input n}

theorem complete_paths
    (W : PathFamilyWitness hn x) {p : Path n} (hp : p ∈ W.paths)
    {u : GridNode n} (hu : u.IsInternal) (hpu : p.Contains u) :
    ∃ v, p.Edge u v ∧ x.ActiveEdge u v := by
  let r : Fin n := ⟨u.row.val + 1, hu⟩
  let v : GridNode n := (r, p r)
  have hpathEdge : p.Edge u v := by
    refine ⟨?_, hpu, ?_⟩
    · rfl
    · rfl
  exact ⟨v, hpathEdge, (W.activeEdge_iff u v).mpr ⟨p, hp, hpathEdge⟩⟩

theorem active_iff_on_path
    (W : PathFamilyWitness hn x) (u : GridNode n) :
    x.Active u ↔ ∃ p ∈ W.paths, p.Contains u := by
  constructor
  · rintro (⟨v, hedge⟩ | ⟨hlast, _hsucc⟩)
    · obtain ⟨p, hp, hpedge⟩ := (W.activeEdge_iff u v).mp hedge
      exact ⟨p, hp, hpedge.2.1⟩
    · exact (W.activeLast_iff u hlast).mp (Or.inr ⟨hlast, _hsucc⟩)
  · rintro ⟨p, hp, hpu⟩
    rcases u.internal_or_last with hu | hu
    · obtain ⟨v, _hpedge, hedge⟩ := W.complete_paths hp hu hpu
      exact Or.inl ⟨v, hedge⟩
    · exact (W.activeLast_iff u hu).mpr ⟨p, hp, hpu⟩

end PathFamilyWitness

theorem pathFamily_disjoint_paths
    {n : ℕ} {hn : 0 < n} {x : Input n}
    (W : PathFamilyWitness hn x) {p q : Path n}
    (hp : p ∈ W.paths) (hq : q ∈ W.paths) (hpq : p ≠ q) :
    ∀ r, p r ≠ q r :=
  W.pairwiseDisjoint p hp q hq hpq

theorem pathFamily_distinguished_path
    {n : ℕ} {hn : 0 < n} {x : Input n}
    (W : PathFamilyWitness hn x) :
    ∃! p : Path n,
      p ∈ W.paths ∧ p ⟨0, hn⟩ = ⟨0, hn⟩ := by
  obtain ⟨p, hp, hpzero⟩ := W.distinguished
  refine ⟨p, ⟨hp, hpzero⟩, ?_⟩
  intro q hq
  by_contra hqp
  have hdisjoint := W.pairwiseDisjoint q hq.1 p hp hqp
  exact (hdisjoint ⟨0, hn⟩) (hq.2.trans hpzero.symm)

theorem pathFamily_no_internal_sink
    {n : ℕ} {hn : 0 < n} {x : Input n}
    (W : PathFamilyWitness hn x) :
    ∀ v, ¬x.ProperSink v := by
  intro v hsink
  obtain ⟨hnotActive, u, hedge⟩ := hsink
  obtain ⟨p, hp, hpedge⟩ := (W.activeEdge_iff u v).mp hedge
  exact hnotActive ((W.active_iff_on_path v).mpr ⟨p, hp, hpedge.2.2⟩)

theorem pathFamily_solutions_last_row
    {n : ℕ} {hn : 0 < n} {x : Input n} {o : Output n}
    (W : PathFamilyWitness hn x) (ho : Valid hn x o) :
    ∃ u, o = Output.activeLast u ∧
      u.IsLastRow ∧ x.Active u := by
  cases o with
  | inactiveSource =>
      obtain ⟨p, hp, hpzero⟩ := W.distinguished
      have hcontains : p.Contains (GridNode.distinguished hn) := by
        exact hpzero
      have hactive : x.Active (GridNode.distinguished hn) :=
        (W.active_iff_on_path (GridNode.distinguished hn)).mpr ⟨p, hp, hcontains⟩
      exact (ho hactive).elim
  | activeLast u =>
      exact ⟨u, rfl, ho⟩
  | properSink v =>
      exact ((pathFamily_no_internal_sink W v) ho).elim

end SoPL

end Revres
