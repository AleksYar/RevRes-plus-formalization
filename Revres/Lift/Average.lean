import Revres.Lift.Formula
import Revres.RevRes.Endpoint
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact gadget-fiber averaging

This file averages pointwise RevRes endpoint identities over the finite fibers of the indexing
gadget. All counting is kept over natural numbers until the final real-valued identities.
-/

namespace Revres

open Lemma53

variable {N : ℕ}

noncomputable local instance clauseFalsifiedDecidable
    (C : Clause N) (z : Fin N → F2) : Decidable (C.Falsified z) :=
  Classical.propDecidable _

noncomputable local instance liftedClauseFalsifiedDecidable
    (L : LiftedClause N) (X : V N) : Decidable (L.Falsified X) :=
  Classical.propDecidable _

/-- The uniform average of a real-valued function over one gadget fiber. -/
noncomputable def fiberAverage
    (N : ℕ) (f : V N → ℝ) (z : Fin N → F2) : ℝ :=
  (∑ X : gadgetFiber N z, f X.1) / (4 : ℝ) ^ N

@[simp] theorem fiberAverage_zero (z : Fin N → F2) :
    fiberAverage N (fun _ => 0) z = 0 := by
  simp [fiberAverage]

theorem fiberAverage_add (f g : V N → ℝ) (z : Fin N → F2) :
    fiberAverage N (fun X => f X + g X) z =
      fiberAverage N f z + fiberAverage N g z := by
  rw [fiberAverage, Finset.sum_add_distrib, add_div]
  rfl

theorem fiberAverage_finset_sum {ι : Type*} [Fintype ι]
    (f : ι → V N → ℝ) (z : Fin N → F2) :
    fiberAverage N (fun X => ∑ i, f i X) z =
      ∑ i, fiberAverage N (f i) z := by
  simp only [fiberAverage, Finset.sum_div]
  rw [Finset.sum_comm]

theorem fiberAverage_const (r : ℝ) (z : Fin N → F2) :
    fiberAverage N (fun _ => r) z = r := by
  rw [fiberAverage, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [gadgetFiber_card]
  norm_num

namespace Clause

/-- The real-valued indicator that an outer assignment falsifies a base clause. -/
noncomputable def realFalsifiedIndicator (C : Clause N) (z : Fin N → F2) : ℝ :=
  if C.Falsified z then 1 else 0

end Clause

/-- Assignments in a gadget fiber which falsify a fixed lifted clause. -/
def liftedFalsifyingFiber
    (N : ℕ) (L : LiftedClause N) (z : Fin N → F2) : Set (V N) :=
  gadgetFiber N z ∩ {X | L.Falsified X}

/-- The allowed blocks at one coordinate of a lifted falsifying fiber. -/
def liftedFiberCoordinate
    (L : LiftedClause N) (z : Fin N → F2) (i : Fin N) :=
  {t : Block // blockEval t = z i ∧ ∀ u, L i = some u → t = u}

noncomputable local instance liftedFiberCoordinateFintype
    (L : LiftedClause N) (z : Fin N → F2) (i : Fin N) :
    Fintype (liftedFiberCoordinate L z i) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- A lifted falsifying fiber is the product of its coordinatewise allowed-block types. -/
def liftedFalsifyingFiberEquiv (L : LiftedClause N) (z : Fin N → F2) :
    liftedFalsifyingFiber N L z ≃ ∀ i : Fin N, liftedFiberCoordinate L z i := by
  refine (Equiv.subtypeEquivRight (fun X => ?_)).trans Equiv.subtypePiEquivPi
  change (gadgetN N X = z ∧ L.Falsified X) ↔
    ∀ i, blockEval (X i) = z i ∧ ∀ u, L i = some u → X i = u
  constructor
  · rintro ⟨hfiber, hfalse⟩ i
    exact ⟨congrFun hfiber i, hfalse i⟩
  · intro h
    exact ⟨funext fun i => (h i).1, fun i => (h i).2⟩

theorem liftedFiberCoordinate_card {C : Clause N} {L : LiftedClause N}
    {z : Fin N → F2} (hL : L ∈ liftClause C) (hC : C.Falsified z) (i : Fin N) :
    Fintype.card (liftedFiberCoordinate L z i) =
      match C i with
      | none => 4
      | some _ => 1 := by
  classical
  have hLift : L.IsLiftOf C := (mem_liftClause_iff C L).1 hL
  have hi := hLift i
  cases hCi : C i with
  | none =>
      have hLi : L i = none := by
        cases hLi : L i with
        | none => rfl
        | some t => simp [hCi, hLi, LiftedClause.blockOptionCompatible] at hi
      let e : liftedFiberCoordinate L z i ≃ {t : Block // blockEval t = z i} :=
        Equiv.subtypeEquivRight fun t => by simp [hLi]
      rw [Fintype.card_congr e, blockFiber_card]
  | some b =>
      cases hLi : L i with
      | none => simp [hCi, hLi, LiftedClause.blockOptionCompatible] at hi
      | some t =>
          have ht : blockEval t = b := by
            simpa [hCi, hLi, LiftedClause.blockOptionCompatible] using hi
          have hz : z i = b := hC i b hCi
          let default : liftedFiberCoordinate L z i :=
            ⟨t, ht.trans hz.symm, fun u hu => Option.some.inj (hLi.symm.trans hu)⟩
          letI : Unique (liftedFiberCoordinate L z i) :=
            { default := default
              uniq := fun s => Subtype.ext (s.property.2 t hLi) }
          exact Fintype.card_unique

/-- Exact size of the part of a gadget fiber falsifying one truth-table lift. -/
theorem liftedClause_fiber_ncard {C : Clause N} {L : LiftedClause N}
    {z : Fin N → F2} (hL : L ∈ liftClause C) :
    (liftedFalsifyingFiber N L z).ncard =
      if C.Falsified z then 4 ^ (N - C.width) else 0 := by
  classical
  by_cases hC : C.Falsified z
  · simp only [if_pos hC]
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_congr (liftedFalsifyingFiberEquiv L z), Fintype.card_pi]
    simp_rw [liftedFiberCoordinate_card hL hC]
    calc
      (∏ i : Fin N, match C i with | none => 4 | some _ => 1) =
          ∏ i : Fin N, if i ∈ C.support then 1 else 4 := by
        apply Finset.prod_congr rfl
        intro i _
        cases hCi : C i <;> simp [hCi]
      _ = 4 ^ (N - C.width) := by
        rw [Finset.prod_ite]
        simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
        have hfilter : Finset.univ.filter (fun i : Fin N => i ∉ C.support) =
            Finset.univ \ C.support := by
          ext i
          simp
        rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ C.support)]
        simp [Clause.width]
  · simp only [if_neg hC]
    have hempty : liftedFalsifyingFiber N L z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro X hX
      rcases hX with ⟨hfiber, hfalse⟩
      apply hC
      have hbase : C.Falsified (gadgetN N X) :=
        (exists_falsified_mem_liftClause_iff C X).1 ⟨L, hL, hfalse⟩
      have hgadget : gadgetN N X = z := hfiber
      rwa [hgadget] at hbase
    rw [hempty]
    simp

/-- Filtering the gadget-fiber subtype is equivalent to taking the corresponding intersection. -/
def fiberPredicateEquiv (p : V N → Prop) (z : Fin N → F2) :
    {X : gadgetFiber N z // p X.1} ≃
      {X : V N // X ∈ gadgetFiber N z ∩ {X | p X}} where
  toFun X := ⟨X.1.1, X.1.2, X.2⟩
  invFun X := ⟨⟨X.1, X.2.1⟩, X.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A real Boolean sum over a gadget fiber is the cardinality of the selected intersection. -/
theorem fiberAverage_indicator_eq_ncard (p : V N → Prop) [DecidablePred p]
    (z : Fin N → F2) :
    fiberAverage N (fun X => if p X then (1 : ℝ) else 0) z =
      ((gadgetFiber N z ∩ {X | p X}).ncard : ℝ) / (4 : ℝ) ^ N := by
  rw [fiberAverage]
  congr 1
  calc
    (∑ X : gadgetFiber N z, if p X.1 then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun X : gadgetFiber N z => p X.1).card : ℝ) := by
      simp
    _ = (Fintype.card {X : gadgetFiber N z // p X.1} : ℝ) := by
      rw [Fintype.card_subtype]
    _ = ((gadgetFiber N z ∩ {X | p X}).ncard : ℝ) := by
      congr 1
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      exact Fintype.card_congr (fiberPredicateEquiv p z)

/-- The exact uniform average of the falsification indicator of one truth-table lift. -/
theorem average_liftedClause {C : Clause N} {L : LiftedClause N}
    {z : Fin N → F2} (hL : L ∈ liftClause C) :
    fiberAverage N (fun X => if L.Falsified X then (1 : ℝ) else 0) z =
      (1 / (4 : ℝ) ^ C.width) * C.realFalsifiedIndicator z := by
  rw [fiberAverage_indicator_eq_ncard]
  change ((liftedFalsifyingFiber N L z).ncard : ℝ) / (4 : ℝ) ^ N = _
  rw [liftedClause_fiber_ncard hL]
  by_cases hC : C.Falsified z
  · simp only [if_pos hC, Clause.realFalsifiedIndicator]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    exact pow_sub_mul_pow (4 : ℝ) (Clause.width_le C)
  · simp [hC, Clause.realFalsifiedIndicator]

/-- The converted parity clause has the same exact average as its lifted-clause presentation. -/
theorem average_liftedParityClause {C : Clause N} {L : LiftedClause N}
    {z : Fin N → F2} (hL : L ∈ liftClause C) :
    fiberAverage N
        (fun X => if L.toParityClause.Falsified X then (1 : ℝ) else 0) z =
      (1 / (4 : ℝ) ^ C.width) * C.realFalsifiedIndicator z := by
  simpa only [LiftedClause.toParityClause_falsified_iff] using average_liftedClause hL (z := z)

/-- The natural falsification indicator casts to its real Boolean indicator. -/
theorem cast_falsifiedIndicator (B : ParityClause (V N)) (X : V N) :
    (falsifiedIndicator B X : ℝ) = if B.Falsified X then 1 else 0 := by
  simp [falsifiedIndicator]

/-- Averaging a parity-clause indicator is its falsifying affine-space density. -/
theorem average_parityClause_eq_density (B : ParityClause (V N))
    (z : Fin N → F2) :
    fiberAverage N (fun X => if B.Falsified X then (1 : ℝ) else 0) z =
      density N B.falsifyingAffine z := by
  rw [fiberAverage_indicator_eq_ncard]
  unfold density
  have hset : gadgetFiber N z ∩ {X | B.Falsified X} =
      (B.falsifyingAffine : Set (V N)) ∩ gadgetFiber N z := by
    ext X
    rw [Set.mem_inter_iff, Set.mem_inter_iff]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hfiber, hfalse⟩
      exact ⟨(ParityClause.mem_falsifyingAffine_iff B X).2 hfalse, hfiber⟩
    · rintro ⟨haffine, hfiber⟩
      exact ⟨hfiber, (ParityClause.mem_falsifyingAffine_iff B X).1 haffine⟩
  rw [hset]

/-- Initial clause occurrences indexed by a base clause and one of its truth-table lifts. -/
abbrev LiftIndex (F : CNF N) :=
  Σ C : ↑F, ↑(liftClause C.1)

namespace LiftIndex

/-- The parity clause carried by a lifted-clause occurrence index. -/
def toParityClause {F : CNF N} (p : LiftIndex F) : ParityClause (V N) :=
  p.2.1.toParityClause

end LiftIndex

/-- The aggregate nonnegative coefficient of one base clause after fiber averaging. -/
noncomputable def liftCoefficient {F : CNF N}
    (α : LiftIndex F → ℕ) (C : ↑F) : ℝ :=
  (1 / (4 : ℝ) ^ C.1.width) *
    ∑ L : ↑(liftClause C.1), (α ⟨C, L⟩ : ℝ)

theorem liftCoefficient_nonneg {F : CNF N}
    (α : LiftIndex F → ℕ) (C : ↑F) :
    0 ≤ liftCoefficient α C := by
  apply mul_nonneg
  · exact div_nonneg zero_le_one (pow_nonneg (by norm_num) _)
  · exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The initial blackboard with the prescribed multiplicity for every lifted occurrence index. -/
def liftedInitialBlackboard (F : CNF N) (α : LiftIndex F → ℕ) : Blackboard (V N) :=
  blackboardOfMultiplicities LiftIndex.toParityClause α

/-- Sum of falsifying affine-space densities over a final multiset, retaining multiplicity. -/
noncomputable def finalDensitySum
    (N : ℕ) (R : Blackboard (V N)) (z : Fin N → F2) : ℝ :=
  (R.map fun B => density N B.falsifyingAffine z).sum

theorem fiberAverage_const_mul (r : ℝ) (f : V N → ℝ) (z : Fin N → F2) :
    fiberAverage N (fun X => r * f X) z = r * fiberAverage N f z := by
  unfold fiberAverage
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Averaging a residual blackboard gives the multiset sum of its clause densities. -/
theorem average_falsifiedCount (R : Blackboard (V N)) (z : Fin N → F2) :
    fiberAverage N (fun X => (falsifiedCount R X : ℝ)) z =
      finalDensitySum N R z := by
  induction R using Multiset.induction_on with
  | empty => simp [finalDensitySum]
  | @cons B R ih =>
      simp only [falsifiedCount, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add]
      rw [fiberAverage_add]
      simp_rw [cast_falsifiedIndicator]
      rw [average_parityClause_eq_density]
      change density N B.falsifyingAffine z +
        fiberAverage N (fun X => (falsifiedCount R X : ℝ)) z = _
      rw [ih]
      simp [finalDensitySum]

/-- The average initial falsification count grouped by its underlying base clauses. -/
theorem average_liftedInitialBlackboard (F : CNF N) (α : LiftIndex F → ℕ)
    (z : Fin N → F2) :
    fiberAverage N
        (fun X => (falsifiedCount (liftedInitialBlackboard F α) X : ℝ)) z =
      ∑ C : ↑F, liftCoefficient α C * C.1.realFalsifiedIndicator z := by
  calc
    fiberAverage N
        (fun X => (falsifiedCount (liftedInitialBlackboard F α) X : ℝ)) z =
        fiberAverage N (fun X =>
          ∑ p : LiftIndex F,
            (α p : ℝ) * if (LiftIndex.toParityClause p).Falsified X then 1 else 0) z := by
      congr 1
      funext X
      rw [liftedInitialBlackboard, falsifiedCount_blackboardOfMultiplicities]
      norm_num only [Nat.cast_sum, Nat.cast_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [cast_falsifiedIndicator]
    _ = ∑ p : LiftIndex F,
        fiberAverage N
          (fun X => (α p : ℝ) *
            if (LiftIndex.toParityClause p).Falsified X then 1 else 0) z :=
      fiberAverage_finset_sum _ z
    _ = ∑ p : LiftIndex F,
        (α p : ℝ) *
          ((1 / (4 : ℝ) ^ p.1.1.width) * p.1.1.realFalsifiedIndicator z) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [fiberAverage_const_mul]
      exact congrArg ((α p : ℝ) * ·)
        (average_liftedParityClause p.2.2 (z := z))
    _ = ∑ C : ↑F, liftCoefficient α C * C.1.realFalsifiedIndicator z := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro C _
      rw [liftCoefficient]
      calc
        (∑ L : ↑(liftClause C.1),
            (α ⟨C, L⟩ : ℝ) *
              ((1 / (4 : ℝ) ^ C.1.width) * C.1.realFalsifiedIndicator z)) =
            ∑ L : ↑(liftClause C.1),
              ((1 / (4 : ℝ) ^ C.1.width) * (α ⟨C, L⟩ : ℝ)) *
                C.1.realFalsifiedIndicator z := by
          apply Finset.sum_congr rfl
          intro L _
          ring
        _ = ((1 / (4 : ℝ) ^ C.1.width) *
              ∑ L : ↑(liftClause C.1), (α ⟨C, L⟩ : ℝ)) *
                C.1.realFalsifiedIndicator z := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Average a pointwise indexed endpoint identity over every outer gadget fiber. -/
theorem averaged_endpoint_identity
    (F : CNF N)
    (α : LiftIndex F → ℕ)
    (R : Blackboard (V N))
    (q : ℕ)
    (hpoint : ∀ X,
      falsifiedCount (liftedInitialBlackboard F α) X =
        q + falsifiedCount R X) :
    ∀ z,
      (∑ C : ↑F,
        liftCoefficient α C * C.1.realFalsifiedIndicator z) =
        (q : ℝ) + finalDensitySum N R z := by
  intro z
  calc
    (∑ C : ↑F, liftCoefficient α C * C.1.realFalsifiedIndicator z) =
        fiberAverage N
          (fun X => (falsifiedCount (liftedInitialBlackboard F α) X : ℝ)) z :=
      (average_liftedInitialBlackboard F α z).symm
    _ = fiberAverage N (fun X => ((q + falsifiedCount R X : ℕ) : ℝ)) z := by
      congr 1
      funext X
      rw [hpoint X]
    _ = fiberAverage N (fun X => (q : ℝ) + (falsifiedCount R X : ℝ)) z := by
      congr 1
      funext X
      norm_num
    _ = (q : ℝ) + finalDensitySum N R z := by
      rw [fiberAverage_add, fiberAverage_const, average_falsifiedCount]

/-- The averaged identity obtained directly from a RevRes derivation and its final endpoint. -/
theorem averaged_endpoint_identity_of_derivation
    (F : CNF N)
    (α : LiftIndex F → ℕ)
    (π : RevDerivation (liftedInitialBlackboard F α) Bₜ)
    (hfinal :
      Bₜ = Multiset.replicate q ([] : ParityClause (V N)) + R) :
    ∀ z,
      (∑ C : ↑F,
        liftCoefficient α C * C.1.realFalsifiedIndicator z) =
        (q : ℝ) + finalDensitySum N R z := by
  apply averaged_endpoint_identity F α R q
  exact static_endpoint_identity π hfinal

end Revres
