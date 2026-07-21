import Lemma53.Junta
import Mathlib.Tactic.DeriveFintype

/-!
# Canonical conical-junta terms

A term is represented by the partial Boolean assignment that it enforces.  This removes the
irrelevant values outside a cube witness's support and makes semantically identical cube terms
definitionally comparable.
-/

namespace Revres

open Lemma53

/-- A conjunction of Boolean literals, represented by its canonical partial assignment. -/
@[ext]
structure Term (N : ℕ) where
  val : Fin N → Option F2
deriving DecidableEq, Fintype

namespace Term

variable {N : ℕ}

/-- The coordinates on which a term imposes a literal. -/
def support (t : Term N) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ t.val i ≠ none

/-- The number of literals imposed by a term. -/
def degree (t : Term N) : ℕ :=
  t.support.card

/-- An assignment matches a term when it satisfies every specified literal. -/
def Matches (t : Term N) (z : Fin N → F2) : Prop :=
  ∀ i b, t.val i = some b → z i = b

instance matchesDecidable (t : Term N) (z : Fin N → F2) : Decidable (t.Matches z) :=
  by
    unfold Matches
    infer_instance

/-- The real-valued indicator that an assignment matches a term. -/
def indicator (t : Term N) (z : Fin N → F2) : ℝ :=
  if t.Matches z then 1 else 0

@[simp]
theorem mem_support {t : Term N} {i : Fin N} :
    i ∈ t.support ↔ t.val i ≠ none := by
  simp [support]

@[simp]
theorem not_mem_support {t : Term N} {i : Fin N} :
    i ∉ t.support ↔ t.val i = none := by
  simp [support]

theorem degree_le (t : Term N) : t.degree ≤ N := by
  rw [degree]
  simpa using Finset.card_le_card (Finset.subset_univ t.support)

@[simp]
theorem indicator_eq_one_iff {t : Term N} {z : Fin N → F2} :
    t.indicator z = 1 ↔ t.Matches z := by
  simp [indicator]

@[simp]
theorem indicator_eq_zero_iff {t : Term N} {z : Fin N → F2} :
    t.indicator z = 0 ↔ ¬t.Matches z := by
  simp [indicator]

theorem indicator_nonneg (t : Term N) (z : Fin N → F2) : 0 ≤ t.indicator z := by
  by_cases h : t.Matches z <;> simp [indicator, h]

theorem indicator_le_one (t : Term N) (z : Fin N → F2) : t.indicator z ≤ 1 := by
  by_cases h : t.Matches z <;> simp [indicator, h]

/-- The canonical term represented by an existing cube witness. -/
def ofCube (U : Finset (Fin N)) (α : Fin N → F2) : Term N :=
  ⟨fun i ↦ if i ∈ U then some (α i) else none⟩

@[simp]
theorem support_ofCube (U : Finset (Fin N)) (α : Fin N → F2) :
    (ofCube U α).support = U := by
  ext i
  simp [ofCube]

@[simp]
theorem degree_ofCube (U : Finset (Fin N)) (α : Fin N → F2) :
    (ofCube U α).degree = U.card := by
  simp [degree]

theorem indicator_ofCube (U : Finset (Fin N)) (α z : Fin N → F2) :
    (ofCube U α).indicator z = cubeIndicator N U α z := by
  by_cases h : ∀ i ∈ U, z i = α i
  · have hmatch : (ofCube U α).Matches z := by
      intro i b hib
      by_cases hi : i ∈ U
      · have hab : α i = b := by
          simpa [ofCube, hi] using hib
        exact (h i hi).trans hab
      · simp [ofCube, hi] at hib
    rw [indicator, cubeIndicator, if_pos hmatch, if_pos h]
  · have hmatch : ¬(ofCube U α).Matches z := by
      intro hterm
      apply h
      intro i hi
      exact hterm i (α i) (by simp [ofCube, hi])
    rw [indicator, cubeIndicator, if_neg hmatch, if_neg h]

/-- Complete unspecified coordinates by zero. -/
def completion (t : Term N) : Fin N → F2 :=
  fun i ↦ (t.val i).getD 0

theorem ofCube_support_completion (t : Term N) :
    ofCube t.support t.completion = t := by
  ext i
  cases hval : t.val i with
  | none => simp [ofCube, completion, hval]
  | some b => simp [ofCube, completion, hval]

theorem cubeIndicator_support_completion (t : Term N) (z : Fin N → F2) :
    cubeIndicator N t.support t.completion z = t.indicator z := by
  rw [← indicator_ofCube, ofCube_support_completion]

end Term

end Revres
