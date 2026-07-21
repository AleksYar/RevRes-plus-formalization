import Lemma53.Gadget
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card

/-!
# Part C: conical juntas

Formalizes §3 of `Lemma53.txt`: cube indicators `τ_{U,α}`, conical juntas of degree at most
`R`, and the general representation lemma (item 18 of §18): every nonnegative function
depending only on coordinates in a set `U` with `|U| ≤ R` is a degree-`R` conical junta.
-/

namespace Lemma53

variable (N : ℕ)

/-- The cube indicator `τ_{U,α}(z) = 1[z|_U = α|_U]`. -/
def cubeIndicator (U : Finset (Fin N)) (α : Fin N → F2) (z : Fin N → F2) : ℝ :=
  if ∀ i ∈ U, z i = α i then 1 else 0

/-- `f` depends only on the coordinates in `U`. -/
def DependsOn (U : Finset (Fin N)) (f : (Fin N → F2) → ℝ) : Prop :=
  ∀ z w : Fin N → F2, (∀ i ∈ U, z i = w i) → f z = f w

/-- `J` is a conical junta of degree at most `R`: a finite nonnegative combination of
cube indicators `τ_{U_k,α_k}` with `|U_k| ≤ R`. -/
def IsConicalJunta (R : ℕ) (J : (Fin N → F2) → ℝ) : Prop :=
  ∃ (ι : Type) (_inst : Fintype ι) (U : ι → Finset (Fin N)) (α : ι → (Fin N → F2))
    (lam : ι → ℝ),
    (∀ k, 0 ≤ lam k) ∧ (∀ k, (U k).card ≤ R) ∧
      ∀ z, J z = ∑ k, lam k * cubeIndicator N (U k) (α k) z

/-- **Junta representation lemma.** A nonnegative function depending only on a set `U` of
at most `R` coordinates is a degree-`R` conical junta. -/
theorem isConicalJunta_of_dependsOn {R : ℕ} {U : Finset (Fin N)} (hU : U.card ≤ R)
    {f : (Fin N → F2) → ℝ} (hdep : DependsOn N U f) (hnonneg : ∀ z, 0 ≤ f z) :
    IsConicalJunta N R f := by
  classical
  set g : ({i : Fin N // i ∈ U} → F2) → (Fin N → F2) :=
    fun p i => if h : i ∈ U then p ⟨i, h⟩ else 0 with hg
  refine ⟨{i : Fin N // i ∈ U} → F2, inferInstance, fun _ => U, g, fun p => f (g p),
    fun p => hnonneg _, fun _ => hU, ?_⟩
  intro z
  set p0 : {i : Fin N // i ∈ U} → F2 := fun i => z i.1 with hp0
  have key : ∀ p : {i : Fin N // i ∈ U} → F2, p ≠ p0 →
      f (g p) * cubeIndicator N U (g p) z = 0 := by
    intro p hp
    have hne : ¬ (∀ i ∈ U, z i = g p i) := by
      intro hall
      apply hp
      funext i
      obtain ⟨i, hi⟩ := i
      have hgi : g p i = p ⟨i, hi⟩ := by simp [g, hi]
      have := hall i hi
      rw [hgi] at this
      simpa [p0] using this.symm
    simp [cubeIndicator, hne]
  have hp0term : f (g p0) * cubeIndicator N U (g p0) z = f z := by
    have heq : ∀ i ∈ U, z i = g p0 i := by
      intro i hi
      simp [g, hi, p0]
    have h1 : cubeIndicator N U (g p0) z = 1 := by
      unfold cubeIndicator; rw [if_pos heq]
    rw [h1, mul_one, (hdep z (g p0) heq)]
  have hsum : ∑ p, f (g p) * cubeIndicator N U (g p) z
      = f (g p0) * cubeIndicator N U (g p0) z :=
    Finset.sum_eq_single p0 (fun p _ hp => key p hp)
      (fun h => absurd (Finset.mem_univ p0) h)
  exact (hsum.trans hp0term).symm

/-- The zero function is a degree-`R` conical junta (for every `R`). -/
theorem isConicalJunta_zero (R : ℕ) : IsConicalJunta N R (fun _ : Fin N → F2 => (0:ℝ)) :=
  ⟨PUnit, inferInstance, fun _ => ∅, fun _ => 0, fun _ => 0,
    fun _ => le_refl 0, fun _ => by simp, fun _ => by simp⟩

/-- A degree-`R` conical junta scaled by a nonnegative constant is again a degree-`R` conical
junta. -/
theorem isConicalJunta_const_mul {R : ℕ} {c : ℝ} (hc : 0 ≤ c) {f : (Fin N → F2) → ℝ}
    (hf : IsConicalJunta N R f) : IsConicalJunta N R (fun z => c * f z) := by
  obtain ⟨ι, inst, U, α, lam, hlam, hU, hrepr⟩ := hf
  refine ⟨ι, inst, U, α, fun k => c * lam k, fun k => mul_nonneg hc (hlam k), hU, ?_⟩
  intro z
  simp only [hrepr z, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **Closure under nonnegative combination.** A nonnegative combination, over a finite index
type, of degree-`R` conical juntas is again a degree-`R` conical junta. -/
theorem isConicalJunta_sum {R : ℕ} {ι : Type} [Fintype ι] {c : ι → ℝ} (hc : ∀ k, 0 ≤ c k)
    {f : ι → (Fin N → F2) → ℝ} (hf : ∀ k, IsConicalJunta N R (f k)) :
    IsConicalJunta N R (fun z => ∑ k, c k * f k z) := by
  classical
  choose ιF instF UF αF lamF hlamF hUF hrepr using hf
  letI := instF
  refine ⟨Σ k : ι, ιF k, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p => UF p.1 p.2
  · exact fun p => αF p.1 p.2
  · exact fun p => c p.1 * lamF p.1 p.2
  · rintro ⟨k, j⟩
    exact mul_nonneg (hc k) (hlamF k j)
  · rintro ⟨k, j⟩
    exact hUF k j
  · intro z
    simp only [hrepr]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    simp only [mul_assoc]

/-- The functions on `Fin N` that agree with `α` on `U` are in bijection with the free choices
on the complement of `U`. -/
def cubeEquiv (U : Finset (Fin N)) (α : Fin N → F2) :
    {z : Fin N → F2 // ∀ i ∈ U, z i = α i} ≃ ({i : Fin N // i ∉ U} → F2) where
  toFun := fun z i => z.1 i.1
  invFun := fun f => ⟨fun i => if h : i ∈ U then α i else f ⟨i, h⟩, fun i hi => by simp [hi]⟩
  left_inv := fun z => by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ U
    · simp [h, z.2 i h]
    · simp [h]
  right_inv := fun f => by
    funext i
    simp [i.2]

/-- **Cube-cardinality lemma.** The functions on `Fin N` that agree with `α` on a set `U` number
exactly `2 ^ (N - |U|)`. -/
theorem card_cube (U : Finset (Fin N)) (α : Fin N → F2) :
    Nat.card {z : Fin N → F2 // ∀ i ∈ U, z i = α i} = 2 ^ (N - U.card) := by
  classical
  rw [Nat.card_congr (cubeEquiv N U α), Nat.card_fun]
  have h1 : Nat.card F2 = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have h2 : Nat.card {i : Fin N // i ∉ U} = N - U.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_coe]
  rw [h1, h2]

end Lemma53
