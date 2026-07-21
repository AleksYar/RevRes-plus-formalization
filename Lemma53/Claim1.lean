import Lemma53.Orthogonal
import Lemma53.Junta

/-!
# Part E (finish): Claim 1 — `condDensity A σ` depends only on `z |_{U_σ}`

Formalizes the dependency half of Claim 1 (§11 of `Lemma53.txt`), via the same intrinsic duality
technique used for `t_le_codim` in `Orthogonal.lean`, applied once more to the pair
`selPick σ : Y N →ₗ (Fin N → F2)` / `selSpread σ : (Fin N → F2) →ₗ Y N`, which are mutual adjoints
w.r.t. `dotY`/`dotN`.
-/

namespace Lemma53

variable (N : ℕ)

/-- The standard `F₂`-bilinear pairing on `Fin N → F2`. -/
def dotN : LinearMap.BilinForm F2 (Fin N → F2) :=
  LinearMap.mk₂ F2 (fun x y => ∑ i, x i * y i)
    (fun x y z => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y z => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

theorem dotN_apply (x y : Fin N → F2) : dotN N x y = ∑ i, x i * y i := by simp [dotN]

theorem dotN_symm (x y : Fin N → F2) : dotN N x y = dotN N y x := by
  simp [dotN_apply, mul_comm]

/-- The "select" linear map: pick the `σ`-selected coordinate of each block. -/
def selPick (σ : Fin N → F2) : Y N →ₗ[F2] (Fin N → F2) where
  toFun := fun y i => if σ i = 0 then (y i).1 else (y i).2
  map_add' := fun y1 y2 => by funext i; by_cases h : σ i = 0 <;> simp [h]
  map_smul' := fun c y => by funext i; by_cases h : σ i = 0 <;> simp [h]

theorem selPick_apply (σ : Fin N → F2) (y : Y N) (i : Fin N) :
    selPick N σ y i = if σ i = 0 then (y i).1 else (y i).2 := rfl

/-- `selPick σ` computes the same thing as the gadget evaluation after fixing `s = σ`. -/
theorem selPick_eq_gadgetN (σ : Fin N → F2) (y : Y N) :
    selPick N σ y = gadgetN N (combine N σ y) := by
  funext i
  simp [selPick_apply, gadgetN, combine, blockEval, gadget]

/-- `selPick σ` and `selSpread σ` are mutually adjoint w.r.t. `dotN`/`dotY`. -/
theorem dotN_selPick_eq_dotY_selSpread (σ : Fin N → F2) (q : Fin N → F2) (y : Y N) :
    dotN N q (selPick N σ y) = dotY N (selSpread N σ q) y := by
  rw [dotN_apply, dotY_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [selPick_apply, selSpread]
  by_cases h : σ i = 0 <;> simp [h]

/-- `blockSupport (selSpread σ q)` is exactly the (unselector-independent) support of `q`. -/
theorem blockSupport_selSpread (σ : Fin N → F2) (q : Fin N → F2) :
    blockSupport N (selSpread N σ q) = Finset.univ.filter (fun i => q i ≠ 0) := by
  ext i
  simp only [blockSupport, selSpread, Finset.mem_filter, Finset.mem_univ, true_and,
    LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h : σ i = 0 <;> simp [h]

/-- The orthogonal complement (w.r.t. `dotN`) of the image of `directionAfterFix A` under
`selPick σ` is exactly the preimage of `W_σ` under `selSpread σ`. -/
theorem orthogonal_map_selPick_eq (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) :
    (dotN N).orthogonal (Submodule.map (selPick N σ) (directionAfterFix N A))
      = Submodule.comap (selSpread N σ) (W N A σ) := by
  ext q
  constructor
  · intro hq
    have hmem : selSpread N σ q ∈ W N A σ := by
      refine Submodule.mem_inf.mpr ⟨?_, LinearMap.mem_range.mpr ⟨q, rfl⟩⟩
      intro d hd
      have h0 : dotN N (selPick N σ d) q = 0 := hq (selPick N σ d) ⟨d, hd, rfl⟩
      rw [dotN_symm, dotN_selPick_eq_dotY_selSpread] at h0
      rw [dotY_symm]
      exact h0
    exact hmem
  · intro hq
    obtain ⟨hL, -⟩ := Submodule.mem_inf.mp hq
    intro v hv
    obtain ⟨d, hd, rfl⟩ := hv
    rw [dotN_symm, dotN_selPick_eq_dotY_selSpread, dotY_symm]
    exact hL d hd

/-- Every `q` orthogonal to the image of `directionAfterFix A` under `selPick σ` has support
contained in `U_σ`. -/
theorem support_subset_U (A : AffineSubspace F2 (V N)) (σ : Fin N → F2)
    {q : Fin N → F2} (hq : q ∈ (dotN N).orthogonal (Submodule.map (selPick N σ)
      (directionAfterFix N A))) :
    Finset.univ.filter (fun i => q i ≠ 0) ⊆ U N A σ := by
  rw [← blockSupport_selSpread N σ q]
  rw [orthogonal_map_selPick_eq] at hq
  classical
  unfold U
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨selSpread N σ q, hq⟩, hi⟩

theorem dotN_single (x : Fin N → F2) (i : Fin N) : dotN N x (Pi.single i 1) = x i := by
  rw [dotN_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem dotN_isRefl : (dotN N).IsRefl := fun x y h => (dotN_symm N y x).trans h

/-- `dotN` is nondegenerate: it separates points via the standard basis vectors. -/
theorem dotN_nondegenerate : (dotN N).Nondegenerate := by
  have h : ∀ x : Fin N → F2, (∀ y, dotN N x y = 0) → x = 0 := by
    intro x hx
    funext i
    exact (dotN_single N x i).symm.trans (hx _)
  exact ⟨h, fun y hy => h y fun x => by rw [dotN_symm]; exact hy x⟩

/-- `combine σ ⁻¹' A`, tested at a point `y` relative to any known member `p` of it, is
characterized purely by `directionAfterFix A` (independent of `σ` beyond `p`, `y`). -/
theorem combine_preimage_iff (A : AffineSubspace F2 (V N)) (σ : Fin N → F2)
    {p : Y N} (hp : combine N σ p ∈ (A : Set (V N))) (y : Y N) :
    combine N σ y ∈ (A : Set (V N)) ↔ y - p ∈ directionAfterFix N A := by
  rw [directionAfterFix, Submodule.mem_comap]
  have hkey : ιY N (y - p) = combine N σ y - combine N σ p := by
    funext i; simp [combine, ιY]
  rw [hkey, ← AffineSubspace.vadd_mem_iff_mem_direction (combine N σ y - combine N σ p) hp,
    vadd_eq_add, sub_add_cancel]
  exact Iff.rfl

/-- **Claim 1 (dependency half).** `condDensity A σ` depends only on `z |_{U_σ}`. -/
theorem condDensity_dependsOn (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) :
    DependsOn N (U N A σ) (fun z => condDensity N A σ z) := by
  have main : ∀ z w : Fin N → F2, (∀ i ∈ U N A σ, z i = w i) →
      condDensity N A σ z ≤ condDensity N A σ w := by
    intro z w hzw
    have hS : z - w ∈ Submodule.map (selPick N σ) (directionAfterFix N A) := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal (dotN_nondegenerate N) (dotN_isRefl N)
        (Submodule.map (selPick N σ) (directionAfterFix N A))]
      intro q hq
      have hsupp := support_subset_U N A σ hq
      rw [dotN_symm, dotN_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : q i = 0
      · simp [hi]
      · have hiF : i ∈ Finset.univ.filter (fun j => q j ≠ 0) := by simp [hi]
        simp [Pi.sub_apply, hzw i (hsupp hiF)]
    obtain ⟨d0, hd0mem, hd0eq⟩ := hS
    have hmaps : ∀ y ∈ (combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z),
        y - d0 ∈ (combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N w) := by
      intro y hy
      obtain ⟨hyA, hyz⟩ := hy
      refine ⟨?_, ?_⟩
      · rw [combine_preimage_iff N A σ hyA (y - d0)]
        have heq : y - d0 - y = -d0 := by abel
        rw [heq]
        exact Submodule.neg_mem _ hd0mem
      · change gadgetN N (combine N σ (y - d0)) = w
        rw [← selPick_eq_gadgetN, map_sub, hd0eq]
        have hyz' : selPick N σ y = z := by
          rw [selPick_eq_gadgetN]; exact hyz
        rw [hyz']
        abel
    have hinj : Set.InjOn (fun y : Y N => y - d0)
        ((combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z)) :=
      fun a _ b _ hab => by simpa using hab
    have hle := Set.ncard_le_ncard_of_injOn (fun y => y - d0) hmaps hinj
      (Set.toFinite _)
    have hle' : (((combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z)).ncard : ℝ)
        ≤ (((combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N w)).ncard : ℝ) := by
      exact_mod_cast hle
    unfold condDensity
    gcongr
  intro z w hzw
  exact le_antisymm (main z w hzw) (main w z fun i hi => (hzw i hi).symm)

/-- Select a single bit from a block, according to a selector bit. -/
def selectBit (c : F2) (t : F2 × F2) : F2 := if c = 0 then t.1 else t.2

theorem selPick_apply' (σ : Fin N → F2) (y : Y N) (i : Fin N) :
    selPick N σ y i = selectBit (σ i) (y i) := rfl

/-- The fiber of a single block's selection has exactly `2` elements. -/
theorem card_selectBit_fiber (c b : F2) :
    Fintype.card {t : F2 × F2 // selectBit c t = b} = 2 := by
  unfold selectBit
  by_cases h : c = 0
  · simp only [h, if_true]
    have e : {t : F2 × F2 // t.1 = b} ≃ F2 :=
      { toFun := fun t => t.1.2
        invFun := fun x => ⟨(b, x), rfl⟩
        left_inv := fun t => by obtain ⟨⟨t1, t2⟩, ht⟩ := t; subst ht; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e]
    exact ZMod.card 2
  · simp only [h, if_false]
    have e : {t : F2 × F2 // t.2 = b} ≃ F2 :=
      { toFun := fun t => t.1.1
        invFun := fun x => ⟨(x, b), rfl⟩
        left_inv := fun t => by obtain ⟨⟨t1, t2⟩, ht⟩ := t; subst ht; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e]
    exact ZMod.card 2

/-- The `selPick σ`-fiber over `z` (as a `Set`) is finite. -/
noncomputable instance (σ z : Fin N → F2) :
    Fintype ↥({y : Y N | selPick N σ y = z}) :=
  Fintype.ofFinite _

/-- The `selPick σ`-fiber over `z` is in bijection with a product of per-block fibers. -/
def selPickFiberEquiv (σ z : Fin N → F2) :
    ↥({y : Y N | selPick N σ y = z}) ≃ ∀ i : Fin N, {t : F2 × F2 // selectBit (σ i) t = z i} :=
  (Equiv.subtypeEquivRight (fun y => by
    simp only [Set.mem_setOf_eq, funext_iff, selPick_apply'])).trans Equiv.subtypePiEquivPi

/-- The `selPick σ`-fiber over `z` has exactly `2 ^ N` elements. -/
theorem card_selPick_fiber (σ z : Fin N → F2) :
    Fintype.card ↥({y : Y N | selPick N σ y = z}) = 2 ^ N := by
  rw [Fintype.card_congr (selPickFiberEquiv N σ z), Fintype.card_pi]
  simp [card_selectBit_fiber]

theorem ncard_selPick_fiber (σ z : Fin N → F2) :
    ({y : Y N | selPick N σ y = z}).ncard = 2 ^ N := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_selPick_fiber]

/-- **`h_{A,σ}(z) ≤ 1`.** -/
theorem condDensity_le_one (A : AffineSubspace F2 (V N)) (σ z : Fin N → F2) :
    condDensity N A σ z ≤ 1 := by
  unfold condDensity
  rw [div_le_one (pow_pos (by norm_num) N)]
  have heq : (combine N σ) ⁻¹' (gadgetFiber N z) = {y : Y N | selPick N σ y = z} := by
    ext y
    simp [gadgetFiber, selPick_eq_gadgetN]
  have hsub : (combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z)
      ⊆ (combine N σ) ⁻¹' (gadgetFiber N z) :=
    Set.preimage_mono Set.inter_subset_right
  have h1 : ((combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z)).ncard
      ≤ ((combine N σ) ⁻¹' (gadgetFiber N z)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((combine N σ) ⁻¹' (gadgetFiber N z)).ncard = 2 ^ N := by
    rw [heq, ncard_selPick_fiber]
  have h1' : (((combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z)).ncard : ℝ)
      ≤ (((combine N σ) ⁻¹' (gadgetFiber N z)).ncard : ℝ) := by exact_mod_cast h1
  rw [h2] at h1'
  exact_mod_cast h1'

end Lemma53
