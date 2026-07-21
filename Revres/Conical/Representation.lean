import Revres.Conical.Term
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Explicit conical-junta representations

This file identifies the existential finite-family definition of `Lemma53.IsConicalJunta` with
nonnegative finitely supported coefficient functions on canonical terms.
-/

namespace Revres

open Lemma53
open scoped BigOperators

/-- A finite real linear combination of canonical terms. -/
abbrev JuntaRep (N : ℕ) := Term N →₀ ℝ

namespace JuntaRep

variable {N degree : ℕ}

/-- Every coefficient in the representation is nonnegative. -/
def Nonnegative (JR : JuntaRep N) : Prop :=
  ∀ t, 0 ≤ JR t

/-- Every term with a nonzero coefficient has degree at most `degree`. -/
def DegreeLE (JR : JuntaRep N) (degree : ℕ) : Prop :=
  ∀ t ∈ JR.support, t.degree ≤ degree

/-- Evaluate a finitely supported term representation on an assignment. -/
def eval (JR : JuntaRep N) : (Fin N → F2) → ℝ :=
  fun z ↦ JR.sum fun t coeff ↦ coeff * t.indicator z

@[simp]
theorem eval_apply (JR : JuntaRep N) (z : Fin N → F2) :
    JR.eval z = JR.sum fun t coeff ↦ coeff * t.indicator z :=
  rfl

@[simp]
theorem eval_zero (z : Fin N → F2) :
    (0 : JuntaRep N).eval z = 0 := by
  simp [eval]

theorem eval_add (JR KR : JuntaRep N) (z : Fin N → F2) :
    (JR + KR).eval z = JR.eval z + KR.eval z := by
  classical
  apply Finsupp.sum_add_index'
  · intro t
    simp
  · intro t a b
    rw [add_mul]

@[simp]
theorem eval_single (t : Term N) (coeff : ℝ) (z : Fin N → F2) :
    eval (Finsupp.single t coeff : JuntaRep N) z = coeff * t.indicator z := by
  classical
  rw [eval, Finsupp.sum_single_index]
  simp

namespace Nonnegative

theorem zero : Nonnegative (0 : JuntaRep N) := by
  intro t
  simp

theorem single {t : Term N} {coeff : ℝ} (hcoeff : 0 ≤ coeff) :
    Nonnegative (Finsupp.single t coeff : JuntaRep N) := by
  classical
  intro u
  by_cases h : t = u
  · subst u
    simpa using hcoeff
  · simp [h]

theorem add {JR KR : JuntaRep N} (hJR : JR.Nonnegative) (hKR : KR.Nonnegative) :
    (JR + KR).Nonnegative := by
  intro t
  exact add_nonneg (hJR t) (hKR t)

theorem finset_sum {ι : Type*} (s : Finset ι) (f : ι → JuntaRep N)
    (hf : ∀ i ∈ s, (f i).Nonnegative) :
    (∑ i ∈ s, f i).Nonnegative := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (N := N))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

end Nonnegative

namespace DegreeLE

theorem zero : DegreeLE (0 : JuntaRep N) degree := by
  intro t ht
  simp at ht

theorem single {t : Term N} {coeff : ℝ} (ht : t.degree ≤ degree) :
    DegreeLE (Finsupp.single t coeff : JuntaRep N) degree := by
  intro u hu
  have hut : u = t := (Finsupp.mem_support_single u t coeff).mp hu |>.1
  simpa [hut] using ht

theorem add {JR KR : JuntaRep N} (hJR : JR.DegreeLE degree) (hKR : KR.DegreeLE degree) :
    (JR + KR).DegreeLE degree := by
  intro t ht
  rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
  · exact hJR t ht
  · exact hKR t ht

theorem finset_sum {ι : Type*} (s : Finset ι) (f : ι → JuntaRep N)
    (hf : ∀ i ∈ s, (f i).DegreeLE degree) :
    (∑ i ∈ s, f i).DegreeLE degree := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (N := N) (degree := degree))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

end DegreeLE

theorem eval_nonneg {JR : JuntaRep N} (hJR : JR.Nonnegative) (z : Fin N → F2) :
    0 ≤ JR.eval z := by
  rw [eval, Finsupp.sum]
  exact Finset.sum_nonneg fun t _ ↦ mul_nonneg (hJR t) (Term.indicator_nonneg t z)

/-- Convert an arbitrary finite cube family to a representation.  Equal canonical terms are
merged by addition in the `Finsupp`. -/
noncomputable def ofFamily {ι : Type*} [Fintype ι]
    (U : ι → Finset (Fin N))
    (α : ι → (Fin N → F2))
    (coeff : ι → ℝ) : JuntaRep N :=
  ∑ k, Finsupp.single (Term.ofCube (U k) (α k)) (coeff k)

theorem eval_finset_sum {ι : Type*} (s : Finset ι) (f : ι → JuntaRep N)
    (z : Fin N → F2) :
    eval (∑ i ∈ s, f i) z = ∑ i ∈ s, eval (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      calc
        eval (∑ j ∈ insert i s, f j) z = eval (f i + ∑ j ∈ s, f j) z := by
          rw [Finset.sum_insert hi]
        _ = eval (f i) z + eval (∑ j ∈ s, f j) z := eval_add _ _ z
        _ = eval (f i) z + ∑ j ∈ s, eval (f j) z := by rw [ih]
        _ = ∑ j ∈ insert i s, eval (f j) z := by rw [Finset.sum_insert hi]

theorem eval_ofFamily {ι : Type*} [Fintype ι]
    (U : ι → Finset (Fin N))
    (α : ι → (Fin N → F2))
    (coeff : ι → ℝ)
    (z : Fin N → F2) :
    (ofFamily U α coeff).eval z =
      ∑ k, coeff k * cubeIndicator N (U k) (α k) z := by
  classical
  rw [ofFamily, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_single, Term.indicator_ofCube]

theorem nonnegative_ofFamily {ι : Type*} [Fintype ι]
    (U : ι → Finset (Fin N))
    (α : ι → (Fin N → F2))
    (coeff : ι → ℝ)
    (hcoeff : ∀ k, 0 ≤ coeff k) :
    (ofFamily U α coeff).Nonnegative := by
  classical
  apply Nonnegative.finset_sum
  intro k _
  exact Nonnegative.single (hcoeff k)

theorem degreeLE_ofFamily {ι : Type*} [Fintype ι]
    (U : ι → Finset (Fin N))
    (α : ι → (Fin N → F2))
    (coeff : ι → ℝ)
    (hdegree : ∀ k, (U k).card ≤ degree) :
    (ofFamily U α coeff).DegreeLE degree := by
  classical
  apply DegreeLE.finset_sum
  intro k _
  apply DegreeLE.single
  simpa using hdegree k

end JuntaRep

variable {N degree : ℕ} {J : (Fin N → Lemma53.F2) → ℝ}

/-- Convert the finite-family witness of `IsConicalJunta` to a canonical `Finsupp`. -/
theorem exists_juntaRep_of_isConicalJunta
    (hJ : Lemma53.IsConicalJunta N degree J) :
    ∃ JR : JuntaRep N,
      JR.Nonnegative ∧
      JR.DegreeLE degree ∧
      JR.eval = J := by
  obtain ⟨ι, inst, U, α, coeff, hcoeff, hdegree, hrepr⟩ := hJ
  letI := inst
  refine ⟨JuntaRep.ofFamily U α coeff,
    JuntaRep.nonnegative_ofFamily U α coeff hcoeff,
    JuntaRep.degreeLE_ofFamily U α coeff hdegree, ?_⟩
  funext z
  exact (JuntaRep.eval_ofFamily U α coeff z).trans (hrepr z).symm

/-- A nonnegative bounded-degree canonical representation supplies an `IsConicalJunta` witness. -/
theorem isConicalJunta_of_juntaRep {JR : JuntaRep N}
    (hcoeff : JR.Nonnegative)
    (hdegree : JR.DegreeLE degree) :
    Lemma53.IsConicalJunta N degree JR.eval := by
  classical
  refine ⟨↑JR.support, inferInstance,
    fun t ↦ t.1.support,
    fun t ↦ t.1.completion,
    fun t ↦ JR t.1,
    ?_, ?_, ?_⟩
  · intro t
    exact hcoeff t.1
  · intro t
    exact hdegree t.1 t.2
  · intro z
    rw [JuntaRep.eval, Finsupp.sum, ← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro t _
    rw [Term.cubeIndicator_support_completion]

/-- Exact equivalence between the old finite-family API and canonical representations. -/
theorem isConicalJunta_iff_exists_rep :
    Lemma53.IsConicalJunta N degree J ↔
    ∃ JR : JuntaRep N,
      JR.Nonnegative ∧
      JR.DegreeLE degree ∧
      JR.eval = J := by
  constructor
  · exact exists_juntaRep_of_isConicalJunta
  · rintro ⟨JR, hnonnegative, hdegree, rfl⟩
    exact isConicalJunta_of_juntaRep hnonnegative hdegree

namespace Lemma53.IsConicalJunta

/-- Directional method form of `exists_juntaRep_of_isConicalJunta`. -/
theorem exists_rep (hJ : Lemma53.IsConicalJunta N degree J) :
    ∃ JR : JuntaRep N,
      JR.Nonnegative ∧ JR.DegreeLE degree ∧ JR.eval = J :=
  exists_juntaRep_of_isConicalJunta hJ

end Lemma53.IsConicalJunta

namespace JuntaRep

/-- Directional method form of `isConicalJunta_of_juntaRep`. -/
theorem isConicalJunta {JR : JuntaRep N}
    (hcoeff : JR.Nonnegative) (hdegree : JR.DegreeLE degree) :
    Lemma53.IsConicalJunta N degree JR.eval :=
  isConicalJunta_of_juntaRep hcoeff hdegree

end JuntaRep

end Revres
