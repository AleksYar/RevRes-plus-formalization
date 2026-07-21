import Lemma53.Selector
import Lemma53.Density
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Part E: the row space `L` and its dimension bound `t ≤ r`

Formalizes §7 and §10 of `Lemma53.txt`. Rather than choosing an explicit full-row-rank matrix
system `M_s s + M_y y = c` representing `A` (as §7 does informally), `L` is defined directly and
intrinsically as the orthogonal complement, w.r.t. the standard `F₂`-bilinear pairing on the
data-bit space `Y N`, of the direction of `A` after fixing the selector part. This is
definitionally independent of any selector vector `σ`, matching the remark at the end of §7 that
`L` "does not depend on the selector assignment".
-/

namespace Lemma53

variable (N : ℕ)

/-- The standard `F₂`-bilinear pairing on the data-bit space `Y N`. -/
def dotY : LinearMap.BilinForm F2 (Y N) :=
  LinearMap.mk₂ F2 (fun y1 y2 => ∑ i, ((y1 i).1 * (y2 i).1 + (y1 i).2 * (y2 i).2))
    (fun y1 y2 y3 => by simp [add_mul, Finset.sum_add_distrib]; ring)
    (fun c y1 y2 => by
      simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring)
    (fun y1 y2 y3 => by simp [mul_add, Finset.sum_add_distrib]; ring)
    (fun c y1 y2 => by
      simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring)

theorem dotY_apply (y1 y2 : Y N) :
    dotY N y1 y2 = ∑ i, ((y1 i).1 * (y2 i).1 + (y1 i).2 * (y2 i).2) := by simp [dotY]

theorem dotY_symm (y1 y2 : Y N) : dotY N y1 y2 = dotY N y2 y1 := by
  simp [dotY_apply, mul_comm]

theorem dotY_single_fst (y : Y N) (i : Fin N) :
    dotY N y (Pi.single i ((1 : F2), (0 : F2))) = (y i).1 := by
  rw [dotY_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem dotY_single_snd (y : Y N) (i : Fin N) :
    dotY N y (Pi.single i ((0 : F2), (1 : F2))) = (y i).2 := by
  rw [dotY_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- `dotY` is nondegenerate: it separates points via the standard basis vectors. -/
theorem dotY_nondegenerate : (dotY N).Nondegenerate := by
  have h : ∀ y : Y N, (∀ y', dotY N y y' = 0) → y = 0 := by
    intro y hy
    funext i
    have h0 : (y i).1 = 0 := (dotY_single_fst N y i).symm.trans (hy _)
    have h1 : (y i).2 = 0 := (dotY_single_snd N y i).symm.trans (hy _)
    exact Prod.ext h0 h1
  exact ⟨h, fun y hy => h y fun x => by rw [dotY_symm]; exact hy x⟩

/-- The linear embedding of the data space into the full gadget-block space, with the selector
part fixed to `0`. -/
def ιY : Y N →ₗ[F2] V N where
  toFun := combine N 0
  map_add' := fun y1 y2 => by funext i; simp [combine]
  map_smul' := fun c y => by funext i; simp [combine]

/-- The direction of `A` after fixing the selector part (independent of which selector `σ` is
fixed to, per the remark at the end of §7). -/
def directionAfterFix (A : AffineSubspace F2 (V N)) : Submodule F2 (Y N) :=
  A.direction.comap (ιY N)

theorem directionAfterFix_eq_ker (A : AffineSubspace F2 (V N)) :
    directionAfterFix N A = LinearMap.ker (A.direction.mkQ.comp (ιY N)) := by
  ext y
  simp [directionAfterFix, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- `L := rowspan(M_y)`, defined intrinsically as the orthogonal complement (w.r.t. `dotY`) of
the direction of `A` after fixing the selector part. -/
noncomputable def rowspanL (A : AffineSubspace F2 (V N)) : Submodule F2 (Y N) :=
  (dotY N).orthogonal (directionAfterFix N A)

/-- `L` is finite (a submodule of the finite type `Y N`). -/
noncomputable instance instFintypeRowspanL (A : AffineSubspace F2 (V N)) :
    Fintype (rowspanL N A) :=
  Fintype.ofFinite _

/-- `t := dim L`. -/
noncomputable def t (A : AffineSubspace F2 (V N)) : ℕ :=
  Module.finrank F2 (rowspanL N A)

/-- **`t ≤ r`.** -/
theorem t_le_codim (A : AffineSubspace F2 (V N)) : t N A ≤ codim N A := by
  have ht : t N A
      = Module.finrank F2 (Y N) - Module.finrank F2 (directionAfterFix N A) := by
    unfold t rowspanL
    rw [LinearMap.BilinForm.finrank_orthogonal (dotY_nondegenerate N)]
  have hrn : Module.finrank F2 (LinearMap.range (A.direction.mkQ.comp (ιY N)))
      + Module.finrank F2 (LinearMap.ker (A.direction.mkQ.comp (ιY N)))
      = Module.finrank F2 (Y N) :=
    LinearMap.finrank_range_add_finrank_ker _
  rw [← directionAfterFix_eq_ker] at hrn
  have hrange_le : Module.finrank F2 (LinearMap.range (A.direction.mkQ.comp (ιY N)))
      ≤ Module.finrank F2 (V N ⧸ A.direction) :=
    Submodule.finrank_le _
  have hquot : Module.finrank F2 (V N ⧸ A.direction) + Module.finrank F2 A.direction
      = Module.finrank F2 (V N) :=
    Submodule.finrank_quotient_add_finrank A.direction
  unfold codim
  omega

/-! ## §9-10: the selected-coordinate subspace `E_σ`, `W_σ`, and block support -/

/-- The linear "spread" map: given a selector `σ`, embed `q ∈ F₂^N` into the data space by
placing `q_i` in the selected coordinate of block `i` and `0` in the unselected coordinate. -/
def selSpread (σ : Fin N → F2) : (Fin N → F2) →ₗ[F2] Y N where
  toFun := fun q i => if σ i = 0 then (q i, 0) else (0, q i)
  map_add' := fun q1 q2 => by funext i; by_cases h : σ i = 0 <;> simp [h]
  map_smul' := fun c q => by funext i; by_cases h : σ i = 0 <;> simp [h]

/-- `E_σ := span{e_{i,σ_i} : i ∈ [N]}`, realized as the range of `selSpread σ`. -/
def E (σ : Fin N → F2) : Submodule F2 (Y N) := LinearMap.range (selSpread N σ)

/-- `W_σ := L ⊓ E_σ`. -/
noncomputable def W (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) : Submodule F2 (Y N) :=
  rowspanL N A ⊓ E N σ

/-- `W_σ` is finite (a submodule of the finite type `Y N`). -/
noncomputable instance instFintypeW (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) :
    Fintype (W N A σ) :=
  Fintype.ofFinite _

/-- The block support of a data vector `w`: the blocks where `w` is nonzero. -/
def blockSupport (w : Y N) : Finset (Fin N) := Finset.univ.filter (fun i => w i ≠ (0, 0))

open Classical in
/-- `U_σ := ⋃_{w ∈ W_σ} bsupp(w)`. -/
noncomputable def U (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∃ w : W N A σ, i ∈ blockSupport N (w : Y N))

end Lemma53
