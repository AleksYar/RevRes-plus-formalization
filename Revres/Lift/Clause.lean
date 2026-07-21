import Lemma53.Density
import Revres.CNF.Formula
import Revres.RevRes.Clause
import Mathlib.Data.List.FinRange

/-!
# Lifted clauses

This file represents partial assignments of gadget blocks and converts them to parity clauses with
the same falsifying assignments.
-/

namespace Revres

open Lemma53
open scoped CharTwo

variable {N : ℕ}

/-- A lifted clause fixes a complete gadget block at each coordinate in its support. -/
abbrev LiftedClause (N : ℕ) := Fin N → Option Block

namespace LiftedClause

/-- An internal assignment falsifies a lifted clause when it extends every fixed block. -/
def Falsified (D : LiftedClause N) (X : V N) : Prop :=
  ∀ i t, D i = some t → X i = t

end LiftedClause

/-- Projection to the selector bit in block `i`. -/
def selectorForm (i : Fin N) : V N →ₗ[F2] F2 where
  toFun X := (X i).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection to the left data bit in block `i`. -/
def leftDataForm (i : Fin N) : V N →ₗ[F2] F2 where
  toFun X := (X i).2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection to the right data bit in block `i`. -/
def rightDataForm (i : Fin N) : V N →ₗ[F2] F2 where
  toFun X := (X i).2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A parity equation falsified exactly when `lhs` has value `b`. -/
def fixingEquation (lhs : V N →ₗ[F2] F2) (b : F2) : ParityEquation (V N) :=
  ⟨lhs, b + 1⟩

@[simp] theorem fixingEquation_falsified_iff
    (lhs : V N →ₗ[F2] F2) (b : F2) (X : V N) :
    (fixingEquation lhs b).Falsified X ↔ lhs X = b := by
  simp [fixingEquation, ParityEquation.Falsified]

/-- The three parity equations whose simultaneous falsification fixes block `i` to `t`. -/
def blockFixingClause (i : Fin N) (t : Block) : ParityClause (V N) :=
  [fixingEquation (selectorForm i) t.1,
    fixingEquation (leftDataForm i) t.2.1,
    fixingEquation (rightDataForm i) t.2.2]

@[simp] theorem blockFixingClause_falsified_iff (i : Fin N) (t : Block) (X : V N) :
    (blockFixingClause i t).Falsified X ↔ X i = t := by
  simp only [blockFixingClause, ParityClause.Falsified, fixingEquation_falsified_iff,
    selectorForm, leftDataForm, rightDataForm, and_true]
  constructor
  · rintro ⟨hs, hl, hr⟩
    exact Prod.ext hs (Prod.ext hl hr)
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun b => b.2.1) h, congrArg (fun b => b.2.2) h⟩

namespace ParityClause

@[simp] theorem falsified_append (A B : ParityClause (V N)) (X : V N) :
    Falsified (A ++ B) X ↔ Falsified A X ∧ Falsified B X := by
  induction A with
  | nil => simp [Falsified]
  | cons e A ih =>
      change (e.Falsified X ∧ Falsified (A ++ B) X) ↔
        (e.Falsified X ∧ Falsified A X) ∧ Falsified B X
      rw [ih]
      constructor
      · rintro ⟨he, hA, hB⟩
        exact ⟨⟨he, hA⟩, hB⟩
      · rintro ⟨⟨he, hA⟩, hB⟩
        exact ⟨he, hA, hB⟩

end ParityClause

namespace LiftedClause

/-- Convert fixed blocks at the listed coordinates into parity equations. -/
def toParityClauseAux (D : LiftedClause N) : List (Fin N) → ParityClause (V N)
  | [] => []
  | i :: is =>
      match D i with
      | none => toParityClauseAux D is
      | some t => blockFixingClause i t ++ toParityClauseAux D is

/-- Convert a lifted clause to a parity clause in the natural coordinate order. -/
def toParityClause (D : LiftedClause N) : ParityClause (V N) :=
  toParityClauseAux D (List.finRange N)

theorem toParityClauseAux_falsified_iff
    (D : LiftedClause N) (is : List (Fin N)) (X : V N) :
    (toParityClauseAux D is).Falsified X ↔
      ∀ i ∈ is, ∀ t, D i = some t → X i = t := by
  induction is with
  | nil => simp [toParityClauseAux]
  | cons i is ih =>
      cases hDi : D i with
      | none =>
          rw [toParityClauseAux]
          simp only [hDi]
          constructor
          · intro h j hj t hDj
            rcases List.mem_cons.mp hj with rfl | hj
            · simp [hDi] at hDj
            · exact (ih.mp h) j hj t hDj
          · intro h
            apply ih.mpr
            intro j hj t hDj
            exact h j (List.mem_cons_of_mem i hj) t hDj
      | some t =>
          rw [toParityClauseAux]
          simp only [hDi, ParityClause.falsified_append, blockFixingClause_falsified_iff]
          constructor
          · rintro ⟨hXi, hrest⟩ j hj s hDj
            rcases List.mem_cons.mp hj with rfl | hj
            · cases Option.some.inj (hDi.symm.trans hDj)
              exact hXi
            · exact (ih.mp hrest) j hj s hDj
          · intro h
            refine ⟨h i (by simp) t hDi, ?_⟩
            apply ih.mpr
            intro j hj s hDj
            exact h j (List.mem_cons_of_mem i hj) s hDj

@[simp] theorem toParityClause_falsified_iff (D : LiftedClause N) (X : V N) :
    D.toParityClause.Falsified X ↔ D.Falsified X := by
  rw [toParityClause, toParityClauseAux_falsified_iff]
  constructor
  · intro h i t hDi
    exact h i (List.mem_finRange i) t hDi
  · intro h i _ t hDi
    exact h i t hDi

/-- Compatibility of one base-clause coordinate with one lifted-clause coordinate. -/
def blockOptionCompatible (c : Option F2) (d : Option Block) : Prop :=
  match c, d with
  | none, none => True
  | some b, some t => blockEval t = b
  | _, _ => False

instance (c : Option F2) (d : Option Block) : Decidable (blockOptionCompatible c d) := by
  cases c <;> cases d <;> unfold blockOptionCompatible <;> infer_instance

/-- `D` is one truth-table lift of `C`: it has the same support and every fixed block evaluates to
the corresponding falsifying outer bit. -/
def IsLiftOf (D : LiftedClause N) (C : Clause N) : Prop :=
  ∀ i, blockOptionCompatible (C i) (D i)

instance (D : LiftedClause N) (C : Clause N) : Decidable (D.IsLiftOf C) := by
  unfold IsLiftOf
  infer_instance

/-- The unique compatible option at an absent base-clause coordinate. -/
def compatibleNoneEquiv :
    {d : Option Block // blockOptionCompatible none d} ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨none, trivial⟩
  left_inv d := by
    rcases d with ⟨d, hd⟩
    cases d with
    | none => rfl
    | some t => simp [blockOptionCompatible] at hd
  right_inv p := by cases p; rfl

/-- Compatible options at a present coordinate are exactly blocks in the appropriate gadget
fiber. -/
def compatibleSomeEquiv (b : F2) :
    {d : Option Block // blockOptionCompatible (some b) d} ≃
      {t : Block // blockEval t = b} where
  toFun d := by
    rcases d with ⟨d, hd⟩
    cases d with
    | none => simp [blockOptionCompatible] at hd
    | some t => exact ⟨t, hd⟩
  invFun t := ⟨some t, t.property⟩
  left_inv d := by
    rcases d with ⟨d, hd⟩
    cases d with
    | none => simp [blockOptionCompatible] at hd
    | some t => rfl
  right_inv t := by rcases t with ⟨t, ht⟩; rfl

theorem card_blockOptionCompatible (c : Option F2) :
    Fintype.card {d : Option Block // blockOptionCompatible c d} =
      match c with
      | none => 1
      | some _ => 4 := by
  cases c with
  | none =>
      rw [Fintype.card_congr compatibleNoneEquiv]
      rfl
  | some b =>
      rw [Fintype.card_congr (compatibleSomeEquiv b), blockFiber_card]

/-- Lifts of `C` are a dependent product of independent compatible block options. -/
def liftSubtypeEquiv (C : Clause N) :
    {D : LiftedClause N // D.IsLiftOf C} ≃
      ∀ i : Fin N, {d : Option Block // blockOptionCompatible (C i) d} := by
  change {D : ∀ _ : Fin N, Option Block // ∀ i, blockOptionCompatible (C i) (D i)} ≃ _
  exact Equiv.subtypePiEquivPi

end LiftedClause

/-- All truth-table lifted clauses arising from one ordinary clause. -/
def liftClause (C : Clause N) : Finset (LiftedClause N) :=
  Finset.univ.filter fun D => D.IsLiftOf C

@[simp] theorem mem_liftClause_iff (C : Clause N) (D : LiftedClause N) :
    D ∈ liftClause C ↔ D.IsLiftOf C := by
  simp [liftClause]

/-- A lifted clause falsified by `X` exists exactly when the base clause is falsified by the gadget
output of `X`. -/
theorem exists_falsified_mem_liftClause_iff (C : Clause N) (X : V N) :
    (∃ D ∈ liftClause C, D.Falsified X) ↔ C.Falsified (gadgetN N X) := by
  constructor
  · rintro ⟨D, hDlift, hDfalse⟩
    have hLift : D.IsLiftOf C := (mem_liftClause_iff C D).1 hDlift
    intro i b hCi
    have hi := hLift i
    rw [hCi] at hi
    cases hDi : D i with
    | none => simp [LiftedClause.blockOptionCompatible, hDi] at hi
    | some t =>
        have ht : blockEval t = b := by
          simpa [LiftedClause.blockOptionCompatible, hDi] using hi
        have hXi : X i = t := hDfalse i t hDi
        change blockEval (X i) = b
        rw [hXi, ht]
  · intro hCfalse
    let D : LiftedClause N := fun i =>
      match C i with
      | none => none
      | some _ => some (X i)
    have hLift : D.IsLiftOf C := by
      intro i
      cases hCi : C i with
      | none => simp [D, hCi, LiftedClause.blockOptionCompatible]
      | some b =>
          simp only [D, hCi, LiftedClause.blockOptionCompatible]
          exact hCfalse i b hCi
    have hDfalse : D.Falsified X := by
      intro i t hDi
      cases hCi : C i with
      | none => simp [D, hCi] at hDi
      | some b => simpa [D, hCi] using hDi
    exact ⟨D, (mem_liftClause_iff C D).2 hLift, hDfalse⟩

/-- A width-`w` base clause has exactly `4 ^ w` truth-table lifted clauses. -/
theorem card_liftClause (C : Clause N) :
    (liftClause C).card = 4 ^ C.width := by
  classical
  change (Finset.univ.filter fun D : LiftedClause N => D.IsLiftOf C).card = _
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (LiftedClause.liftSubtypeEquiv C), Fintype.card_pi]
  simp_rw [LiftedClause.card_blockOptionCompatible]
  calc
    (∏ i : Fin N, match C i with | none => 1 | some _ => 4) =
        ∏ i : Fin N, if C i ≠ none then 4 else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      cases C i <;> simp
    _ = ∏ i ∈ C.support, 4 := by
      rw [Clause.support, Finset.prod_filter]
    _ = 4 ^ C.width := by simp [Clause.width]

end Revres
