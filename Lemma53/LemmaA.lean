import Lemma53.Density
import Lemma53.LinearAlgebra
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Part I: Lemma A (§4 of `Lemma53.txt`, = `Lemma52.txt` = Lemma 5.2)

Formalizes `Lemma52.txt`, discharging the `lemmaA` hypothesis that `Lemma53/MainLemma.lean` takes
as given. Deviates from `Lemma52.txt`'s own Gaussian-elimination proof sketch: instead of choosing
an explicit full-row-rank matrix and processing pivot blocks "right to left", this proves the same
bound by induction on `N`, peeling off one gadget block at a time via rank-nullity applied to the
`head`/`tail` projections. See CLAUDE.md's "Part I" design note for the full rationale.
-/

open scoped Pointwise

namespace Lemma53

/-! ## The `Block`-level dot product and the local fact -/

/-- The plain (unbundled) dot product on a single gadget block, matching `Lemma52.txt`'s
`a₁s+a₂u+a₃v`. -/
def dot (a t : Block) : F2 := a.1 * t.1 + a.2.1 * t.2.1 + a.2.2 * t.2.2

/-- The bundled bilinear form version of `dot`, used to get orthogonal-complement dimension
counts via `LinearMap.BilinForm.finrank_orthogonal`. -/
def dotBlock : LinearMap.BilinForm F2 Block :=
  LinearMap.mk₂ F2 dot
    (fun a1 a2 t => by simp [dot, add_mul]; ring)
    (fun c a t => by simp [dot, smul_eq_mul]; ring)
    (fun a t1 t2 => by simp [dot, mul_add]; ring)
    (fun c a t => by simp [dot, smul_eq_mul]; ring)

theorem dotBlock_apply (a t : Block) : dotBlock a t = dot a t := by simp [dotBlock]

theorem dotBlock_symm (a t : Block) : dotBlock a t = dotBlock t a := by
  simp [dotBlock_apply, dot]; ring

/-- `dotBlock` is nondegenerate: it separates points via the three standard basis vectors. -/
theorem dotBlock_nondegenerate : dotBlock.Nondegenerate := by
  have h : ∀ a : Block, (∀ t, dotBlock a t = 0) → a = 0 := by
    intro a ha
    have h0 : a.1 = 0 := by have := ha (1, 0, 0); simpa [dotBlock_apply, dot] using this
    have h1 : a.2.1 = 0 := by have := ha (0, 1, 0); simpa [dotBlock_apply, dot] using this
    have h2 : a.2.2 = 0 := by have := ha (0, 0, 1); simpa [dotBlock_apply, dot] using this
    exact Prod.ext h0 (Prod.ext h1 h2)
  exact ⟨h, fun a ha => h a fun t => by rw [dotBlock_symm]; exact ha t⟩

/-- **Local fact.** For `a ≠ 0`, a nonconstant affine equation `dot a t = d` is satisfied by at
most `3` of the `4` points of any single-block gadget fiber. `Block` has only `8` elements, so
this is checked by direct case analysis. -/
theorem fiber_affine_le_three (b d : F2) (a : Block) (ha : a ≠ 0) :
    {t : Block | blockEval t = b ∧ dot a t = d}.ncard ≤ 3 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  fin_cases a <;> try exact absurd rfl ha
  all_goals fin_cases b <;> fin_cases d <;> decide

/-- Every proper submodule of `Block` is contained in some hyperplane `{t | dot a t = 0}` for a
nonzero `a` — via the orthogonal complement w.r.t. `dotBlock`, which is nonzero exactly because
`W` is proper. -/
theorem exists_dot_ne_zero_of_ne_top {W : Submodule F2 Block} (hW : W ≠ ⊤) :
    ∃ a : Block, a ≠ 0 ∧ ∀ w ∈ W, dot a w = 0 := by
  have hlt : W < (⊤ : Submodule F2 Block) := lt_top_iff_ne_top.mpr hW
  have hWlt : Module.finrank F2 W < Module.finrank F2 Block := by
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [finrank_top] at h
  have hfr : Module.finrank F2 (dotBlock.orthogonal W)
      = Module.finrank F2 Block - Module.finrank F2 W :=
    LinearMap.BilinForm.finrank_orthogonal dotBlock_nondegenerate W
  have hpos : 0 < Module.finrank F2 (dotBlock.orthogonal W) := by omega
  have hne : dotBlock.orthogonal W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨a, ha_mem, ha0⟩ := (dotBlock.orthogonal W).ne_bot_iff.mp hne
  refine ⟨a, ha0, fun w hw => ?_⟩
  have h := (LinearMap.BilinForm.mem_orthogonal_iff).mp ha_mem w hw
  rwa [dotBlock_symm, dotBlock_apply] at h

/-- **Block-level coset bound.** If `W` is a proper submodule, a coset `p +ᵥ W` meets any
single-block gadget fiber in at most `3` points (an upper bound only — it doesn't matter whether
`p +ᵥ W` itself is disjoint from the fiber or not). -/
theorem coset_fiber_le_three {W : Submodule F2 Block} (hW : W ≠ ⊤) (p : Block) (b : F2) :
    {t : Block | blockEval t = b ∧ t - p ∈ W}.ncard ≤ 3 := by
  obtain ⟨a, ha, hWa⟩ := exists_dot_ne_zero_of_ne_top hW
  have hsub : {t : Block | blockEval t = b ∧ t - p ∈ W}
      ⊆ {t : Block | blockEval t = b ∧ dot a t = dot a p} := by
    rintro t ⟨htb, htW⟩
    refine ⟨htb, ?_⟩
    have h0 := hWa (t - p) htW
    have hlin : dot a (t - p) = dot a t - dot a p := by simp [dot]; ring
    rwa [hlin, sub_eq_zero] at h0
  calc {t : Block | blockEval t = b ∧ t - p ∈ W}.ncard
      ≤ {t : Block | blockEval t = b ∧ dot a t = dot a p}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 3 := fiber_affine_le_three b (dot a p) a ha

/-! ## Peeling off one gadget block: the `head`/`tail` linear maps -/

theorem finrank_Block : Module.finrank F2 Block = 3 := by
  change Module.finrank F2 (F2 × F2 × F2) = 3
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]

/-- `Set.ncard` version of `blockFiber_card`. -/
theorem blockFiber_ncard (b : F2) : {t : Block | blockEval t = b}.ncard = 4 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact blockFiber_card b

/-- `finrank (V k) = 3 * k`: the ambient space of `k` gadget blocks has dimension `3k`. -/
theorem finrank_V (k : ℕ) : Module.finrank F2 (V k) = 3 * k := by
  rw [Module.finrank_pi_fintype F2, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, finrank_Block, smul_eq_mul, mul_comm]

variable (n : ℕ)

/-- Evaluate at the first block. -/
def headLM : V (n + 1) →ₗ[F2] Block := LinearMap.proj (0 : Fin (n + 1))

/-- Evaluate at every block after the first. -/
def tailLM : V (n + 1) →ₗ[F2] V n :=
  LinearMap.pi (fun i : Fin n => LinearMap.proj (i.succ : Fin (n + 1)))

theorem headLM_apply (X : V (n + 1)) : headLM n X = X 0 := rfl

theorem tailLM_apply (X : V (n + 1)) (i : Fin n) : tailLM n X i = X i.succ := rfl

/-- A gadget-block tuple is determined by its head and tail: `ker head ⊓ ker tail = ⊥`. -/
theorem ker_head_inf_ker_tail :
    (LinearMap.ker (headLM n) ⊓ LinearMap.ker (tailLM n) : Submodule F2 (V (n + 1))) = ⊥ := by
  ext X
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · rintro ⟨h0, h1⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact congrFun h1 j
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- Splitting the `(n+1)`-block gadget fiber condition into a head condition and a tail
condition. -/
theorem mem_gadgetFiber_succ_iff (X : V (n + 1)) (z : Fin (n + 1) → F2) :
    X ∈ gadgetFiber (n + 1) z ↔
      blockEval (headLM n X) = z 0 ∧ tailLM n X ∈ gadgetFiber n (z ∘ Fin.succ) := by
  simp only [gadgetFiber, Set.mem_setOf_eq, gadgetN, headLM_apply, funext_iff, tailLM_apply,
    Function.comp_apply]
  constructor
  · intro h
    refine ⟨h 0, fun i => h i.succ⟩
  · rintro ⟨h0, h1⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact h1 j

/-- A nonempty affine subspace's coset description: `A` is exactly the coset of its own
direction through any of its points. Lets the induction below work entirely with cosets of
submodules, never touching `AffineSubspace.map`/`AffineMap`. -/
theorem coe_eq_vadd_direction {k : ℕ} {A : AffineSubspace F2 (V k)} {x0 : V k} (hx0 : x0 ∈ A) :
    (A : Set (V k)) = x0 +ᵥ (A.direction : Set (V k)) := by
  ext q
  simp only [Set.mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
  constructor
  · intro hq
    refine ⟨q - x0, ?_, by abel⟩
    have h := AffineSubspace.vadd_mem_iff_mem_direction (q - x0) hx0
    rw [vadd_eq_add, show q - x0 + x0 = q from by abel] at h
    exact h.mp hq
  · rintro ⟨d, hd, rfl⟩
    have h := AffineSubspace.vadd_mem_iff_mem_direction d hx0
    rw [vadd_eq_add] at h
    rw [show x0 + d = d + x0 from by abel]
    exact h.mpr hd

/-- **Bounded-fiber counting**, at the `Set.ncard` level: if every fiber of `f` over `s` has size
at most `c`, then `s` itself has size at most `c` times the size of its image. -/
theorem ncard_le_mul_ncard_image {α β : Type*} (s : Set α) (hs : s.Finite) (f : α → β) (c : ℕ)
    (hc : ∀ y ∈ f '' s, {x ∈ s | f x = y}.ncard ≤ c) :
    s.ncard ≤ c * (f '' s).ncard := by
  classical
  have himg : (f '' s).Finite := hs.image f
  rw [Set.ncard_eq_toFinset_card s hs, Set.ncard_eq_toFinset_card (f '' s) himg]
  apply Finset.card_le_mul_card_image_of_maps_to (f := f)
  · intro a ha
    rw [Set.Finite.mem_toFinset] at ha ⊢
    exact Set.mem_image_of_mem f ha
  · intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    have hbound := hc b hb
    have hfin_fiber : ({x ∈ s | f x = b}).Finite := hs.subset (fun x hx => hx.1)
    rw [Set.ncard_eq_toFinset_card _ hfin_fiber] at hbound
    have heq : hs.toFinset.filter (fun a => f a = b) = hfin_fiber.toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [heq]
    exact hbound

/-- **The core combinatorial bound**, proved by induction on `n`, peeling off one gadget block
(the head) at a time. `D` is the direction submodule and `x0` a basepoint, so `x0 +ᵥ D` is the
coset that will eventually stand in for an affine subspace `A`. -/
theorem coset_inter_gadgetFiber_bound :
    ∀ (n : ℕ) (D : Submodule F2 (V n)) (x0 : V n) (z : Fin n → F2),
    ∃ m : ℕ, Module.finrank F2 (V n) ≤ Module.finrank F2 D + 3 * m ∧
      ((x0 +ᵥ (D : Set (V n))) ∩ gadgetFiber n z).ncard * 4 ^ m ≤ 3 ^ m * 4 ^ n := by
  intro n
  induction n with
  | zero =>
    intro D x0 z
    refine ⟨0, by rw [finrank_V]; omega, ?_⟩
    have hcard1 : Nat.card (V 0) = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_pi]; simp
    have hle : ((x0 +ᵥ (D : Set (V 0))) ∩ gadgetFiber 0 z).ncard ≤ 1 := by
      calc ((x0 +ᵥ (D : Set (V 0))) ∩ gadgetFiber 0 z).ncard
          ≤ (Set.univ : Set (V 0)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
        _ = Nat.card (V 0) := Set.ncard_univ _
        _ = 1 := hcard1
    simpa using hle
  | succ n ih =>
    intro D x0 z
    set D' : Submodule F2 (V n) := D.map (tailLM n) with hD'_def
    set Dk : Submodule F2 (V (n + 1)) := D ⊓ LinearMap.ker (tailLM n) with hDk_def
    set D'' : Submodule F2 Block := Dk.map (headLM n) with hD''_def
    set x0' : V n := tailLM n x0 with hx0'_def
    set z' : Fin n → F2 := z ∘ Fin.succ with hz'_def
    set L : Set (V (n + 1)) := (x0 +ᵥ (D : Set (V (n + 1)))) ∩ gadgetFiber (n + 1) z with hL_def
    set S : Set (V n) := (x0' +ᵥ (D' : Set (V n))) ∩ gadgetFiber n z' with hS_def
    -- finrank bookkeeping: finrank D = finrank D' + finrank D''
    have hsplit1 : Module.finrank F2 D' + Module.finrank F2 Dk = Module.finrank F2 D :=
      finrank_map_add_finrank_inf_ker (tailLM n) D
    have hkerinf : (Dk ⊓ LinearMap.ker (headLM n) : Submodule F2 (V (n + 1))) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      rw [Submodule.mem_inf] at hw
      have hw1 : w ∈ LinearMap.ker (tailLM n) := (Submodule.mem_inf.mp hw.1).2
      have hmem : w ∈ (LinearMap.ker (headLM n) ⊓ LinearMap.ker (tailLM n) :
          Submodule F2 (V (n + 1))) := Submodule.mem_inf.mpr ⟨hw.2, hw1⟩
      rw [ker_head_inf_ker_tail] at hmem
      exact hmem
    have hsplit2 : Module.finrank F2 D''
        + Module.finrank F2 (Dk ⊓ LinearMap.ker (headLM n) : Submodule F2 (V (n + 1)))
        = Module.finrank F2 Dk :=
      finrank_map_add_finrank_inf_ker (headLM n) Dk
    rw [hkerinf, finrank_bot, add_zero] at hsplit2
    have hDeq : Module.finrank F2 D = Module.finrank F2 D' + Module.finrank F2 D'' := by omega
    have hfrsucc : Module.finrank F2 (V (n + 1)) = 3 + Module.finrank F2 (V n) := by
      rw [finrank_V, finrank_V]; ring
    -- combinatorial bookkeeping: L maps into S under tailLM, with bounded fibers
    have hcoset : ∀ X1 ∈ L, ∀ X2 ∈ L, tailLM n X1 = tailLM n X2 →
        headLM n X1 - headLM n X2 ∈ D'' := by
      intro X1 hX1 X2 hX2 htaileq
      obtain ⟨d1, hd1, heq1⟩ := Set.mem_vadd_set.mp hX1.1
      obtain ⟨d2, hd2, heq2⟩ := Set.mem_vadd_set.mp hX2.1
      rw [vadd_eq_add] at heq1 heq2
      have hXsub : X1 - X2 = d1 - d2 := by rw [← heq1, ← heq2]; abel
      have hDmem : X1 - X2 ∈ D := hXsub ▸ Submodule.sub_mem D hd1 hd2
      have hkertail : X1 - X2 ∈ LinearMap.ker (tailLM n) := by
        rw [LinearMap.mem_ker, map_sub, htaileq, sub_self]
      have hDkmem : X1 - X2 ∈ Dk := Submodule.mem_inf.mpr ⟨hDmem, hkertail⟩
      have hmem : headLM n (X1 - X2) ∈ D'' := Submodule.mem_map_of_mem hDkmem
      rwa [map_sub] at hmem
    have hheadtailinj : ∀ X1 X2 : V (n + 1), headLM n X1 = headLM n X2 →
        tailLM n X1 = tailLM n X2 → X1 = X2 := by
      intro X1 X2 hh ht
      have hmem : X1 - X2 ∈ (LinearMap.ker (headLM n) ⊓ LinearMap.ker (tailLM n) :
          Submodule F2 (V (n + 1))) := by
        refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · rw [LinearMap.mem_ker, map_sub, hh, sub_self]
        · rw [LinearMap.mem_ker, map_sub, ht, sub_self]
      rw [ker_head_inf_ker_tail, Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have hmaps : ∀ X ∈ L, tailLM n X ∈ S := by
      intro X hX
      obtain ⟨hX1, hX2⟩ := hX
      rw [mem_gadgetFiber_succ_iff] at hX2
      refine ⟨?_, hX2.2⟩
      obtain ⟨d, hd, hXeq⟩ := Set.mem_vadd_set.mp hX1
      rw [vadd_eq_add] at hXeq
      refine Set.mem_vadd_set.mpr ⟨tailLM n d, Submodule.mem_map_of_mem hd, ?_⟩
      rw [vadd_eq_add, ← hXeq, map_add]
    have hfiber_le4 : ∀ Y ∈ tailLM n '' L, {X ∈ L | tailLM n X = Y}.ncard ≤ 4 := by
      rintro Y ⟨X_Y, hX_Y, hXY_eq⟩
      have hsub : headLM n '' {X ∈ L | tailLM n X = Y} ⊆ {t : Block | blockEval t = z 0} := by
        rintro t ⟨X, ⟨hXL, -⟩, rfl⟩
        exact (mem_gadgetFiber_succ_iff n X z |>.mp hXL.2).1
      have hinj : Set.InjOn (headLM n) {X ∈ L | tailLM n X = Y} := fun X1 h1 X2 h2 heq =>
        hheadtailinj X1 X2 heq (h1.2.trans h2.2.symm)
      calc {X ∈ L | tailLM n X = Y}.ncard
          = (headLM n '' {X ∈ L | tailLM n X = Y}).ncard := (hinj.ncard_image).symm
        _ ≤ {t : Block | blockEval t = z 0}.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 4 := blockFiber_ncard (z 0)
    have himg_sub : tailLM n '' L ⊆ S := by rintro Y ⟨X, hX, rfl⟩; exact hmaps X hX
    have himg_le : (tailLM n '' L).ncard ≤ S.ncard := Set.ncard_le_ncard himg_sub (Set.toFinite S)
    by_cases hDtop : D'' = ⊤
    · -- the block is fully free: `m` doesn't grow.
      obtain ⟨m', hm'1, hm'2⟩ := ih D' x0' z'
      have hD''3 : Module.finrank F2 D'' = 3 := by rw [hDtop, finrank_top, finrank_Block]
      refine ⟨m', by omega, ?_⟩
      have hLbound4 : L.ncard ≤ 4 * (tailLM n '' L).ncard :=
        ncard_le_mul_ncard_image L (Set.toFinite L) (tailLM n) 4 hfiber_le4
      calc L.ncard * 4 ^ m' ≤ (4 * (tailLM n '' L).ncard) * 4 ^ m' :=
            Nat.mul_le_mul_right _ hLbound4
        _ ≤ (4 * S.ncard) * 4 ^ m' := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 himg_le)
        _ = 4 * (S.ncard * 4 ^ m') := by ring
        _ ≤ 4 * (3 ^ m' * 4 ^ n) := Nat.mul_le_mul_left 4 hm'2
        _ = 3 ^ m' * 4 ^ (n + 1) := by ring
    · -- the block is genuinely constrained: `m` grows by `1`.
      obtain ⟨m', hm'1, hm'2⟩ := ih D' x0' z'
      have hfiber_le3 : ∀ Y ∈ tailLM n '' L, {X ∈ L | tailLM n X = Y}.ncard ≤ 3 := by
        rintro Y ⟨X_Y, hX_Y, hXY_eq⟩
        have hsub : headLM n '' {X ∈ L | tailLM n X = Y}
            ⊆ {t : Block | blockEval t = z 0 ∧ t - headLM n X_Y ∈ D''} := by
          rintro t ⟨X, ⟨hXL, hXeqY⟩, rfl⟩
          exact ⟨(mem_gadgetFiber_succ_iff n X z |>.mp hXL.2).1,
            hcoset X hXL X_Y hX_Y (hXeqY.trans hXY_eq.symm)⟩
        have hinj : Set.InjOn (headLM n) {X ∈ L | tailLM n X = Y} := fun X1 h1 X2 h2 heq =>
          hheadtailinj X1 X2 heq (h1.2.trans h2.2.symm)
        calc {X ∈ L | tailLM n X = Y}.ncard
            = (headLM n '' {X ∈ L | tailLM n X = Y}).ncard :=
              (hinj.ncard_image).symm
          _ ≤ {t : Block | blockEval t = z 0 ∧ t - headLM n X_Y ∈ D''}.ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ 3 := coset_fiber_le_three hDtop (headLM n X_Y) (z 0)
      refine ⟨m' + 1, by omega, ?_⟩
      have hLbound3 : L.ncard ≤ 3 * (tailLM n '' L).ncard :=
        ncard_le_mul_ncard_image L (Set.toFinite L) (tailLM n) 3 hfiber_le3
      calc L.ncard * 4 ^ (m' + 1) ≤ (3 * (tailLM n '' L).ncard) * 4 ^ (m' + 1) :=
            Nat.mul_le_mul_right _ hLbound3
        _ ≤ (3 * S.ncard) * 4 ^ (m' + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 himg_le)
        _ = 3 * (S.ncard * 4 ^ m') * 4 := by ring
        _ ≤ 3 * (3 ^ m' * 4 ^ n) * 4 := by
            have := Nat.mul_le_mul_left 3 hm'2
            exact Nat.mul_le_mul_right 4 this
        _ = 3 ^ (m' + 1) * 4 ^ (n + 1) := by ring

/-- Bridges the coset-level bound to the actual `AffineSubspace`, matching `codim`'s definition. -/
theorem lemmaA_nat (n : ℕ) (A : AffineSubspace F2 (V n)) (hA : (A : Set (V n)).Nonempty)
    (z : Fin n → F2) :
    ∃ m : ℕ, codim n A ≤ 3 * m ∧
      ((A : Set (V n)) ∩ gadgetFiber n z).ncard * 4 ^ m ≤ 3 ^ m * 4 ^ n := by
  obtain ⟨x0, hx0⟩ := hA
  obtain ⟨m, hm1, hm2⟩ := coset_inter_gadgetFiber_bound n A.direction x0 z
  refine ⟨m, by unfold codim; omega, ?_⟩
  rwa [coe_eq_vadd_direction hx0]

/-! ## Final numeric conversion -/

noncomputable def κ0 : ℝ := (1 / 3) * Real.logb 2 (4 / 3)

theorem κ0_pos : 0 < κ0 := by
  have h : 0 < Real.logb 2 (4 / 3) := Real.logb_pos (by norm_num) (by norm_num)
  unfold κ0
  linarith

theorem rpow_three_quarter_eq (x : ℝ) : (3 / 4 : ℝ) ^ x = (2 : ℝ) ^ (-κ0 * (3 * x)) := by
  have h1 : -κ0 * (3 * x) = Real.logb 2 (4 / 3) * (-x) := by unfold κ0; ring
  rw [h1, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4 / 3), ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  norm_num

/-- **Lemma A** (§4 of `Lemma53.txt`, formalizing `Lemma52.txt` = Lemma 5.2). Discharges the
`lemmaA` hypothesis of `main_lemma`. -/
theorem lemmaA (n : ℕ) (A : AffineSubspace F2 (V n)) (hA : (A : Set (V n)).Nonempty)
    (z : Fin n → F2) : density n A z ≤ (2 : ℝ) ^ (-κ0 * (codim n A : ℝ)) := by
  obtain ⟨m, hm1, hm2⟩ := lemmaA_nat n A hA z
  have hcast : (((A : Set (V n)) ∩ gadgetFiber n z).ncard : ℝ) * 4 ^ m ≤ (3 : ℝ) ^ m * 4 ^ n := by
    exact_mod_cast hm2
  have h4n : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have h4m : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have step_a' : density n A z ≤ (3 / 4 : ℝ) ^ m := by
    unfold density
    rw [div_pow]
    exact (div_le_div_iff₀ h4n h4m).mpr hcast
  have hexp : (codim n A : ℝ) / 3 ≤ (m : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3), mul_comm]
    exact_mod_cast hm1
  have step_b : (3 / 4 : ℝ) ^ (m : ℝ) ≤ (3 / 4 : ℝ) ^ ((codim n A : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hexp
  have step_a : density n A z ≤ (3 / 4 : ℝ) ^ (m : ℝ) := by
    rw [Real.rpow_natCast]
    exact step_a'
  have step_c : (3 / 4 : ℝ) ^ ((codim n A : ℝ) / 3) = (2 : ℝ) ^ (-κ0 * (codim n A : ℝ)) := by
    have h := rpow_three_quarter_eq ((codim n A : ℝ) / 3)
    rwa [show (3 : ℝ) * ((codim n A : ℝ) / 3) = (codim n A : ℝ) from by ring] at h
  calc density n A z ≤ (3 / 4 : ℝ) ^ (m : ℝ) := step_a
    _ ≤ (3 / 4 : ℝ) ^ ((codim n A : ℝ) / 3) := step_b
    _ = (2 : ℝ) ^ (-κ0 * (codim n A : ℝ)) := step_c

end Lemma53
