import Lemma53.Gadget
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Part E (start): linear algebra core over `F₂`

Formalizes item 14 of §18 of `Lemma53.txt`: a consistent linear system `B y = b` over `F₂` has
exactly `2 ^ (n - rank B)` solutions.
-/

namespace Lemma53

variable {n r : ℕ}

private theorem card_F2 : Fintype.card F2 = 2 := ZMod.card 2

/-- The kernel of `B.mulVecLin` has exactly `2 ^ (n - rank B)` elements. -/
theorem card_ker_mulVecLin (B : Matrix (Fin r) (Fin n) F2) :
    Nat.card (LinearMap.ker B.mulVecLin) = 2 ^ (n - B.rank) := by
  classical
  haveI : Fintype (LinearMap.ker B.mulVecLin) := Fintype.ofFinite _
  have hrn : Module.finrank F2 (LinearMap.range B.mulVecLin)
      + Module.finrank F2 (LinearMap.ker B.mulVecLin)
      = Module.finrank F2 (Fin n → F2) :=
    LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hdom : Module.finrank F2 (Fin n → F2) = n := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hrank : Module.finrank F2 (LinearMap.range B.mulVecLin) = B.rank := rfl
  have hker : Module.finrank F2 (LinearMap.ker B.mulVecLin) = n - B.rank := by omega
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F2), card_F2, hker]

/-- **Solution-counting lemma.** Over `F₂`, a consistent linear system `B y = b` has exactly
`2 ^ (n - rank B)` solutions. -/
theorem card_solutionSet {B : Matrix (Fin r) (Fin n) F2} {b : Fin r → F2}
    {y0 : Fin n → F2} (hy0 : B.mulVec y0 = b) :
    Nat.card {y : Fin n → F2 // B.mulVec y = b} = 2 ^ (n - B.rank) := by
  rw [← card_ker_mulVecLin B]
  apply Nat.card_congr
  refine
    { toFun := fun y => ⟨y.1 - y0, by
        change B.mulVec (y.1 - y0) = 0
        rw [Matrix.mulVec_sub, y.2, hy0, sub_self]⟩
      invFun := fun k => ⟨k.1 + y0, by
        have hk0 : B.mulVec k.1 = 0 := k.2
        rw [Matrix.mulVec_add, hk0, zero_add, hy0]⟩
      left_inv := fun y => by simp
      right_inv := fun k => by simp }

/-- Over `F₂`, any finite-dimensional vector space has exactly `2 ^ finrank` elements. -/
theorem nat_card_eq_two_pow_finrank {W : Type*} [AddCommGroup W] [Module F2 W]
    [Module.Finite F2 W] : Nat.card W = 2 ^ Module.finrank F2 W := by
  classical
  let b := Module.Free.chooseBasis F2 W
  haveI : Finite (Module.Free.ChooseBasisIndex F2 W) := Module.Finite.finite_basis b
  haveI : Fintype (Module.Free.ChooseBasisIndex F2 W) := Fintype.ofFinite _
  haveI : Fintype W := Module.fintypeOfFintype b
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F2), card_F2]

/-- **A nonzero `F₂`-linear functional is `1` on exactly half of its (finite) domain.** -/
theorem card_functional_eq_one {W : Type*} [AddCommGroup W] [Module F2 W]
    [Module.Finite F2 W] {φ : W →ₗ[F2] F2} (hφ : φ ≠ 0) :
    2 * Nat.card {w : W // φ w = 1} = Nat.card W := by
  classical
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hcase : ∀ x : F2, x = 0 ∨ x = 1 := by decide
  have hw0' : φ w0 = 1 := (hcase (φ w0)).resolve_left hw0
  have hrange_top : LinearMap.range φ = ⊤ := by
    ext y
    simp only [LinearMap.mem_range, Submodule.mem_top, iff_true]
    exact ⟨y • w0, by rw [map_smul, hw0', smul_eq_mul, mul_one]⟩
  have hrange : Module.finrank F2 (LinearMap.range φ) = 1 := by
    rw [hrange_top, finrank_top, Module.finrank_self]
  have hrn : Module.finrank F2 (LinearMap.range φ) + Module.finrank F2 (LinearMap.ker φ)
      = Module.finrank F2 W := LinearMap.finrank_range_add_finrank_ker φ
  have hker : Module.finrank F2 (LinearMap.ker φ) + 1 = Module.finrank F2 W := by omega
  have hfiber : Nat.card {w : W // φ w = 1} = Nat.card (LinearMap.ker φ) := by
    apply Nat.card_congr
    refine
      { toFun := fun w => ⟨w.1 - w0, by
          change φ (w.1 - w0) = 0
          rw [map_sub, w.2, hw0', sub_self]⟩
        invFun := fun k => ⟨k.1 + w0, by
          have hk0 : φ k.1 = 0 := k.2
          rw [map_add, hk0, zero_add, hw0']⟩
        left_inv := fun w => by simp
        right_inv := fun k => by simp }
  rw [hfiber, nat_card_eq_two_pow_finrank (W := LinearMap.ker φ),
    nat_card_eq_two_pow_finrank (W := W), ← hker, pow_succ']

/-- **Rank-nullity relativized to a submodule of the domain.** For `f : M →ₗ[F₂] N` and
`p ≤ M`, the image `p.map f` and the part of `p` killed by `f` account for all of `p`'s
dimension. Used by Part I to split a direction submodule's dimension across one gadget block
(`f := tail`/`f := head`) without ever constructing an explicit matrix. -/
theorem finrank_map_add_finrank_inf_ker {M N : Type*} [AddCommGroup M] [Module F2 M]
    [Module.Finite F2 M] [AddCommGroup N] [Module F2 N] (f : M →ₗ[F2] N) (p : Submodule F2 M) :
    Module.finrank F2 (p.map f) + Module.finrank F2 (p ⊓ LinearMap.ker f : Submodule F2 M)
      = Module.finrank F2 p := by
  have hrange : LinearMap.range (f.comp p.subtype) = p.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker' : Module.finrank F2 (LinearMap.ker (f.comp p.subtype))
      = Module.finrank F2 (p ⊓ LinearMap.ker f : Submodule F2 M) := by
    rw [LinearMap.ker_comp, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.comp p.subtype)
  rw [hrange, hker'] at hrn
  exact hrn

end Lemma53
