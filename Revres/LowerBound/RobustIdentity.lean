import Lemma53.Lemma53
import Revres.Lift.Average
import Revres.RevRes.Refutation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Robust identity from a RevRes refutation

This file reconstructs surviving lifted-clause multiplicities, decomposes every residual final
clause with `Lemma53.Lemma53`, and assembles the exact identity `P = 1 + J + E`.
-/

namespace Revres

open Lemma53

universe u

variable {N : ℕ}

noncomputable local instance robustIdentityDecidableEqParityClause (N : ℕ) :
    DecidableEq (ParityClause (V N)) := Classical.decEq _

/-- A multiset supported on a finite indexed family has an exact multiplicity function on that
family. No injectivity of the family is required. -/
theorem exists_multiplicities_of_supported
    {X : Type u} [AddCommGroup X] [Module F2 X]
    {ι : Type*} [Fintype ι]
    (D : ι → ParityClause X)
    (A : Blackboard X)
    (hA : ∀ B ∈ A, ∃ i, D i = B) :
    ∃ α : ι → ℕ, blackboardOfMultiplicities D α = A := by
  classical
  letI : DecidableEq ι := Classical.decEq _
  induction A using Multiset.induction_on with
  | empty =>
      refine ⟨fun _ => 0, ?_⟩
      simp [blackboardOfMultiplicities]
  | @cons B A ih =>
      have htail : ∀ C ∈ A, ∃ i, D i = C := by
        intro C hC
        exact hA C (by simp [hC])
      obtain ⟨α, hα⟩ := ih htail
      obtain ⟨i, hi⟩ := hA B (by simp)
      let α' : ι → ℕ := Function.update α i (α i + 1)
      refine ⟨α', ?_⟩
      unfold blackboardOfMultiplicities at hα ⊢
      let f : ι → Blackboard X := fun j => Multiset.replicate (α j) (D j)
      have hfun :
          (fun j => Multiset.replicate (α' j) (D j)) =
            Function.update f i (Multiset.replicate (α i + 1) (D i)) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [α', f]
        · simp [α', f, hji]
      rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i), Multiset.replicate_succ, hi,
        Multiset.cons_add]
      congr 1
      calc
        Multiset.replicate (α i) B + ∑ j ∈ Finset.univ \ {i}, f j =
            Multiset.replicate (α i) (D i) + ∑ j ∈ Finset.univ \ {i}, f j := by
          rw [hi]
        _ =
            ∑ j, f j := by
          rw [Multiset.add_comm]
          simpa [f, Finset.sdiff_singleton_eq_erase] using
            Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
        _ = A := hα

/-- Recover exact truth-table-lift multiplicities for a blackboard supported on `indexLift F`. -/
theorem exists_liftIndex_multiplicities
    (F : CNF N) (A : Blackboard (V N))
    (hA : ∀ B ∈ A, B ∈ indexLift F) :
    ∃ α : LiftIndex F → ℕ, liftedInitialBlackboard F α = A := by
  classical
  apply exists_multiplicities_of_supported LiftIndex.toParityClause A
  intro B hB
  rcases (mem_indexLift_iff F B).1 (hA B hB) with ⟨C, hCF, L, hLC, rfl⟩
  exact ⟨⟨⟨C, hCF⟩, ⟨L, hLC⟩⟩, rfl⟩

namespace RevResRefutation

/-- Recover lift provenance for the canonical initial residual of an index-lift refutation. -/
theorem exists_residualLiftMultiplicities {F : CNF N}
    (π : RevResRefutation (indexLift F)) :
    ∃ α : LiftIndex F → ℕ,
      liftedInitialBlackboard F α = π.initial - π.final := by
  classical
  apply exists_liftIndex_multiplicities F
  intro B hB
  exact π.initial_supported B
    (Multiset.mem_of_le (Multiset.sub_le_self π.initial π.final) hB)

end RevResRefutation

/-- Evaluation of a real linear combination of base-clause falsification indicators. -/
noncomputable def axiomCombination
    (F : CNF N) (coeff : Clause N → ℝ) (z : Fin N → F2) : ℝ :=
  ∑ C ∈ F, coeff C * C.realFalsifiedIndicator z

/-- A function is explicitly represented by nonnegative coefficients on all base clauses. -/
def HasNonnegativeAxiomRepresentation
    (F : CNF N) (P : (Fin N → F2) → ℝ) : Prop :=
  ∃ coeff : Clause N → ℝ,
    (∀ C, 0 ≤ coeff C) ∧
      ∀ z, P z = axiomCombination F coeff z

/-- The pointwise error factor returned by `Lemma53.Lemma53`. -/
noncomputable def decompositionError (degree : ℕ) : ℝ :=
  (2 : ℝ) ^
    (-(min (κ0 / 4) (1 / 4)) * (degree : ℝ))

theorem decompositionError_nonneg (degree : ℕ) :
    0 ≤ decompositionError degree := by
  unfold decompositionError
  exact Real.rpow_nonneg (by norm_num) _

theorem decompositionError_pos (degree : ℕ) :
    0 < decompositionError degree := by
  unfold decompositionError
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- Closure of conical juntas under pointwise addition, derived from the existing finite-sum
closure theorem. -/
theorem isConicalJunta_add {degree : ℕ}
    {J₁ J₂ : (Fin N → F2) → ℝ}
    (hJ₁ : IsConicalJunta N degree J₁)
    (hJ₂ : IsConicalJunta N degree J₂) :
    IsConicalJunta N degree (fun z => J₁ z + J₂ z) := by
  let f : Fin 2 → (Fin N → F2) → ℝ := fun i => if i = 0 then J₁ else J₂
  have hf : ∀ i, IsConicalJunta N degree (f i) := by
    intro i
    fin_cases i <;> simp [f, hJ₁, hJ₂]
  have hsum := isConicalJunta_sum N (ι := Fin 2) (c := fun _ => (1 : ℝ))
    (fun _ => by norm_num) hf
  simpa [f, Fin.sum_univ_two] using hsum

/-- Aggregate the unconditional affine-density decomposition over a residual multiset, preserving
every occurrence multiplicity. -/
theorem finalDensitySum_decomposition
    (degree : ℕ) (R : Blackboard (V N)) :
    ∃ J E : (Fin N → F2) → ℝ,
      (∀ z, finalDensitySum N R z = J z + E z) ∧
      IsConicalJunta N degree J ∧
      (∀ z, 0 ≤ J z ∧ J z ≤ (R.card : ℝ)) ∧
      (∀ z,
        0 ≤ E z ∧
        E z ≤ (R.card : ℝ) * decompositionError degree) := by
  induction R using Multiset.induction_on with
  | empty =>
      refine ⟨fun _ => 0, fun _ => 0, ?_, isConicalJunta_zero N degree, ?_, ?_⟩
      · intro z
        simp [finalDensitySum]
      · intro z
        simp
      · intro z
        simp
  | @cons B R ih =>
      obtain ⟨JB, EB, hBEq, hBJunta, hBBound, hBError⟩ :=
        Lemma53 N degree B.falsifyingAffine
      obtain ⟨JR, ER, hREq, hRJunta, hRBound, hRError⟩ := ih
      refine ⟨fun z => JB z + JR z, fun z => EB z + ER z, ?_,
        isConicalJunta_add hBJunta hRJunta, ?_, ?_⟩
      · intro z
        rw [show finalDensitySum N (B ::ₘ R) z =
          density N B.falsifyingAffine z + finalDensitySum N R z by
            simp [finalDensitySum]]
        rw [hBEq z, hREq z]
        ring
      · intro z
        refine ⟨add_nonneg (hBBound z).1 (hRBound z).1, ?_⟩
        calc
          JB z + JR z ≤ 1 + (R.card : ℝ) :=
            add_le_add ((hBBound z).2.1.trans (hBBound z).2.2) (hRBound z).2
          _ = ((B ::ₘ R).card : ℝ) := by simp [add_comm]
      · intro z
        refine ⟨add_nonneg (hBError z).1 (hRError z).1, ?_⟩
        calc
          EB z + ER z ≤ decompositionError degree +
              (R.card : ℝ) * decompositionError degree := by
            apply add_le_add
            · simpa [decompositionError] using (hBError z).2
            · exact (hRError z).2
          _ = ((B ::ₘ R).card : ℝ) * decompositionError degree := by
            simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
            ring

/-- Divide an averaged endpoint identity by its positive empty-clause multiplicity and aggregate
the final affine decompositions into the robust identity `P = 1 + J + E`. -/
theorem averaged_endpoint_to_robust_identity
    (F : CNF N)
    (α : LiftIndex F → ℕ)
    (R : Blackboard (V N))
    (q degree : ℕ)
    (hq : 1 ≤ q)
    (hpoint : ∀ X,
      falsifiedCount (liftedInitialBlackboard F α) X =
        q + falsifiedCount R X) :
    ∃ P J E : (Fin N → F2) → ℝ,
      HasNonnegativeAxiomRepresentation F P ∧
      (∀ z, P z = 1 + J z + E z) ∧
      IsConicalJunta N degree J ∧
      (∀ z, 0 ≤ J z ∧ J z ≤ (R.card : ℝ)) ∧
      (∀ z,
        0 ≤ E z ∧
        E z ≤ (R.card : ℝ) * decompositionError degree) := by
  classical
  obtain ⟨Jsum, Esum, hdecomp, hJsum, hJbound, hEbound⟩ :=
    finalDensitySum_decomposition (N := N) degree R
  let scale : ℝ := 1 / (q : ℝ)
  let P : (Fin N → F2) → ℝ := fun z =>
    scale * ∑ C : ↑F, liftCoefficient α C * C.1.realFalsifiedIndicator z
  let J : (Fin N → F2) → ℝ := fun z => scale * Jsum z
  let E : (Fin N → F2) → ℝ := fun z => scale * Esum z
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqreal
  have hscale_nonneg : 0 ≤ scale := by
    exact div_nonneg zero_le_one hqpos.le
  have hscale_le_one : scale ≤ 1 := by
    exact (div_le_one hqpos).2 hqreal
  refine ⟨P, J, E, ?_, ?_, ?_, ?_, ?_⟩
  · let coeff : Clause N → ℝ := fun C =>
      if hC : C ∈ F then scale * liftCoefficient α ⟨C, hC⟩ else 0
    refine ⟨coeff, ?_, ?_⟩
    · intro C
      by_cases hC : C ∈ F
      · simp only [coeff, hC, dite_true]
        exact mul_nonneg hscale_nonneg (liftCoefficient_nonneg α ⟨C, hC⟩)
      · simp [coeff, hC]
    · intro z
      calc
        P z = ∑ C : ↑F,
            scale *
              (liftCoefficient α C * C.1.realFalsifiedIndicator z) := by
          simp [P, Finset.mul_sum]
        _ = ∑ C : ↑F, coeff C.1 * C.1.realFalsifiedIndicator z := by
          apply Finset.sum_congr rfl
          intro C _
          simp only [coeff, C.2, dite_true]
          ring
        _ = ∑ C ∈ F, coeff C * C.realFalsifiedIndicator z := by
          symm
          exact Finset.sum_subtype F (fun _ => Iff.rfl)
            (fun C => coeff C * C.realFalsifiedIndicator z)
        _ = axiomCombination F coeff z := rfl
  · intro z
    have havg := averaged_endpoint_identity F α R q hpoint z
    change scale *
        (∑ C : ↑F, liftCoefficient α C * C.1.realFalsifiedIndicator z) =
      1 + scale * Jsum z + scale * Esum z
    rw [havg, hdecomp z]
    dsimp [scale]
    field_simp [ne_of_gt hqpos]
    ring
  · exact isConicalJunta_const_mul N hscale_nonneg hJsum
  · intro z
    refine ⟨mul_nonneg hscale_nonneg (hJbound z).1, ?_⟩
    calc
      scale * Jsum z ≤ 1 * Jsum z :=
        mul_le_mul_of_nonneg_right hscale_le_one (hJbound z).1
      _ = Jsum z := one_mul _
      _ ≤ (R.card : ℝ) := (hJbound z).2
  · intro z
    refine ⟨mul_nonneg hscale_nonneg (hEbound z).1, ?_⟩
    calc
      scale * Esum z ≤ 1 * Esum z :=
        mul_le_mul_of_nonneg_right hscale_le_one (hEbound z).1
      _ = Esum z := one_mul _
      _ ≤ (R.card : ℝ) * decompositionError degree := (hEbound z).2

/-- **Milestone M3.** Every refutation of the truth-table index lift yields an exact robust
identity with explicit nonnegative base-clause coefficients and an exact step-count bound. -/
theorem revres_to_robust_identity
    {F : CNF N}
    (π : RevResRefutation (indexLift F))
    (degree : ℕ) :
    ∃ (P J E : (Fin N → F2) → ℝ) (q : ℕ) (T : ℝ),
      1 ≤ q ∧
      HasNonnegativeAxiomRepresentation F P ∧
      (∀ z, P z = 1 + J z + E z) ∧
      IsConicalJunta N degree J ∧
      (∀ z, 0 ≤ J z ∧ J z ≤ T) ∧
      (∀ z,
        0 ≤ E z ∧
        E z ≤ T * decompositionError degree) ∧
      T ≤ (2 : ℝ) * π.length := by
  classical
  obtain ⟨α, hα⟩ := π.exists_residualLiftMultiplicities
  let q : ℕ := π.emptyMultiplicity
  let R : Blackboard (V N) := π.nonemptyFinalResidual
  have hpoint : ∀ X,
      falsifiedCount (liftedInitialBlackboard F α) X =
        q + falsifiedCount R X := by
    intro X
    rw [hα]
    exact π.residual_pointwise X
  obtain ⟨P, J, E, hP, hidentity, hJ, hJbound, hEbound⟩ :=
    averaged_endpoint_to_robust_identity F α R q degree π.one_le_emptyMultiplicity hpoint
  refine ⟨P, J, E, q, (R.card : ℝ), π.one_le_emptyMultiplicity,
    hP, hidentity, hJ, hJbound, hEbound, ?_⟩
  exact_mod_cast π.nonemptyFinalResidual_card_le

end Revres
