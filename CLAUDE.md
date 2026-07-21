# CLAUDE.md

## Project

Formalizing `Lemma53.txt` — "Affine-to-Conical Decomposition for the 3-Bit Index Gadget", a
research-level combinatorics/linear-algebra lemma — in Lean 4 + Mathlib. `Lemma53.txt` is the
source of truth; section numbers below (`§n`) refer to it. `Lemma53.txt` §18 already contains the
author's own recommended proof order — the plan below follows it, adapted to concrete Lean design
choices made along the way. `Lemma53.txt`'s own Main Lemma depends on a second result, "Lemma A"
(§4), which it takes as an imported fact from a separate manuscript — `Lemma52.txt` is that
manuscript's proof (Lemma 5.2), and Part I formalizes it, discharging the `lemmaA` hypothesis in
`Lemma53/MainLemma.lean` directly instead of assuming it (see `Lemma53.Lemma53` in
`Lemma53/Lemma53.lean`).

## Build

- `lake build Lemma53` or `lake build` — builds the whole project.
- `lake env lean Lemma53/<File>.lean` — fast typecheck of a single file (a few seconds), prefer this
  over a full `lake build` while iterating on one file.
- Toolchain: `leanprover/lean4:v4.32.0` (`lean-toolchain`). Mathlib pinned via `lakefile.toml`
  `rev = "v4.32.0"`.
- Mathlib's prebuilt `.olean` cache was already fetched once (`lake exe cache get`, ~8600 files).
  Re-run it if `lake-manifest.json` changes (e.g. after bumping the Mathlib rev), otherwise Mathlib
  would rebuild from source.

## CRITICAL: never `import Mathlib`

Every file must use targeted imports (e.g. `import Mathlib.Data.Set.Card`), never the umbrella
`import Mathlib`. Even with the prebuilt cache, `import Mathlib` loads all ~8600 Mathlib files and
took **~3 minutes per file** to build; targeted imports build in a few seconds. When adding a new
Mathlib dependency, grep the relevant Mathlib file's own `import`/`public import` header for the
precise module path rather than guessing a broad umbrella import.

## Architecture / file layout

`Lemma53.lean` is the root import file — add new files there too.

- `Lemma53/Gadget.lean` (§1) — `F2 := ZMod 2`, `gadget`, `Block := F2×F2×F2`, `gadgetN`,
  `gadgetFiber`, proves `|Fib(z)| = 4^N` (`gadgetFiber_card`, `gadgetFiber_ncard`).
- `Lemma53/Density.lean` (§2) — `V N := Fin N → Block` (ambient space `(F₂³)^N`), `density A z`
  (paper's `h_A(z)`) for `A : AffineSubspace F2 (V N)`, proves `0 ≤ h_A ≤ 1`.
- `Lemma53/Junta.lean` (§3, §18 item 18) — `cubeIndicator`, `DependsOn`, `IsConicalJunta`,
  `isConicalJunta_of_dependsOn` (general lemma: nonneg + depends on ≤ `R` coords ⟹ degree-`R`
  conical junta).
- `Lemma53/Selector.lean` (§7–9) — `Y N := Fin N → F2×F2` (data bits), `combine`/`splitS`/`splitY`
  (selector/data split of a gadget assignment), `condDensity A σ z` (paper's `h_{A,σ}(z)`),
  `density_eq_avg_condDensity` (identity (1): `h_A = 2^{-N} Σ_σ h_{A,σ}`).
- `Lemma53/LinearAlgebra.lean` (§18 item 14) — generic `n r : ℕ` matrix lemmas: `card_ker_mulVecLin`,
  `card_solutionSet` (solution-counting lemma: consistent `B y = b` over `F2` has exactly
  `2^(n - rank B)` solutions).
- `Lemma53/Orthogonal.lean` (§7, §9–10) — `codim A` (in `Density.lean`), the dot-product `BilinForm`
  `dotY` on `Y N` and its nondegeneracy, `L := rowspanL A` (`t ≤ codim A` proved as `t_le_codim`),
  `E σ`, `W A σ := L ⊓ E σ`, `blockSupport`, `U A σ := ⋃_{w∈W} blockSupport w`. See "Part E design
  pivot" below — this intrinsically derives `L` from `A.direction` rather than choosing an explicit
  matrix system.
- `Lemma53/Claim1.lean` (§11, Claim 1 dependency half) — `dotN` (dot product on `Fin N → F2`),
  `selPick σ` / `selSpread σ` (mutual adjoints w.r.t. `dotN`/`dotY`), and
  `condDensity_dependsOn : DependsOn N (U N A σ) (condDensity N A σ)` — Part E complete for all
  downstream purposes (see "Part E is done" below).
- `Lemma53/GoodBad.lean` (§12–13, Part F) — `good A R σ := (U N A σ).card ≤ R`, `J`/`Err` (paper's
  `J_A`/`E_A`), `density_eq_J_add_Err`, `J_nonneg`, `Err_nonneg`, `J_le_density`, and
  `isConicalJunta_J : IsConicalJunta N R (J N A R)` — **Part F complete**.
- `Junta.lean` also grew three closure lemmas needed by Part F:
  `isConicalJunta_zero`, `isConicalJunta_const_mul` (scale by a nonneg constant), and
  `isConicalJunta_sum` (nonneg combination over a finite index type, via `choose` + a `Σ`-type).
- `Lemma53/LinearAlgebra.lean` also grew two generic facts needed by Part G:
  `nat_card_eq_two_pow_finrank` (any finite-dim `F2`-vector space has `2^finrank` elements, via a
  `Module.Free.chooseBasis`) and `card_functional_eq_one` (a nonzero `F2`-linear functional is `1`
  on exactly half its domain — rank-nullity + a coset-translation bijection, same shape as
  `card_solutionSet` but for a general vector space instead of a matrix kernel).
- `Lemma53/BadSelector.lean` (§14–16, **Part G — complete**) — `evalAt`/`φ` (the evaluation
  functional at a selected coordinate, restricted to `W_σ`), `mem_U_iff_φ_ne_zero` (`i ∈ U_σ ↔ φ_i
  ≠ 0` on `W_σ` — the key bridge from the linear-algebra side to the combinatorial side),
  `sum_blockSupport_eq` (double-counting identity `2·Σ_{w∈W_σ}|bsupp w| = |U_σ|·|W_σ|`, avoiding
  all fractions), **Claim 3** (`exists_wide_of_card_U_gt`): `|U_σ| > R ⟹ ∃ w ∈ W_σ, w ≠ 0 ∧
  2·|bsupp w| > R`; **Claim 4** (`card_sigma_mem_E_le`): for any `w : Y N`,
  `Nat.card {σ // w ∈ E_σ} ≤ 2 ^ (N - |bsupp w|)` — see design note below (only the upper bound
  is proved, not Lemma53.txt's exact-value characterization, and the "uses both coordinates" case
  split from §15 turned out to be unnecessary); **Claim 5** (`card_bad_le_sum` for the
  `Finset`/nat-level union bound over `w ∈ L`, then `card_bad_le_real`): given `4 · t N A ≤ R`,
  `Nat.card {σ // R < |U_σ|} ≤ 2^N · 2^{-R/4}` (as reals — this is the one place in the whole
  project needing `Real.rpow`, since the bound genuinely combines a `/2` factor from Claims 3-4
  with a `/4` factor from `t ≤ R/4`, and Lemma53.txt's own "avoid nat division" advice stops
  applying once the target statement itself has a fractional exponent).
- `Lemma53/Junta.lean` also grew a general counting fact needed by Claim 4: `card_cube` — the
  functions `Fin N → F2` agreeing with a fixed `α` on a set `U` number exactly `2^(N-|U|)`
  (`cubeEquiv` bijects them with free choices on `U`'s complement).

- `Lemma53/MainLemma.lean` (§5–6, §17, **Part H — complete, final assembly**) — `main_lemma`: takes
  Lemma A (§4) as an explicit hypothesis parameter (`lemmaA : ∀ A, (A:Set (V N)).Nonempty → ∀ z,
  density N A z ≤ 2^(-κ0 * codim N A)`), and produces, for every `A`/`R`, a decomposition
  `density N A z = J z + E z` with `J` a degree-`R` conical junta, `0 ≤ J ≤ density ≤ 1`, and
  `0 ≤ E z ≤ 2^(-min(κ0/4, 1/4) * R)`. Three cases: `A` empty (`density_eq_zero_of_empty`, `J=E=0`);
  `A` nonempty and `4·codim A > R` (Step 1: `J:=0, E:=density`, bound via `lemmaA` directly, since
  `κ0 * codim A ≥ (κ0/4)*R ≥ κ*R` when `4·codim A > R`... actually the inequality direction needed is
  `R < 4·codim A ⟹ κ0·codim A ≥ (min(κ0/4,1/4))·R`, proved via `nlinarith`); `A` nonempty and
  `4·codim A ≤ R` (uses all of Parts E–G: `J := J N A R`, `E := Err N A R`, and chains
  `Err_le_real` (new in `BadSelector.lean`, bounds `Err` by the bad-selector fraction) with
  `card_bad_le_real` (Claim 5) to get `Err ≤ 2^(-R/4) ≤ 2^(-κ·R)`).
- `Lemma53/Claim1.lean` also grew `condDensity_le_one` (`0 ≤ h_{A,σ}(z) ≤ 1`, needed to relate `Err`
  to a bad-selector count) — proved via `selectBit`/`card_selectBit_fiber`/`selPickFiberEquiv`, the
  same two-step `Set`-then-`Fintype.card_congr` pattern as `gadgetFiber_ncard`, giving
  `ncard_selPick_fiber : |{y // selPick σ y = z}| = 2^N` unconditionally (no dependence on `A`).
- `Lemma53/BadSelector.lean` also grew `Err_le_real` (`Err N A R z ≤ Nat.card {σ // bad} / 2^N`),
  bridging Part F's `Err` to Part G's Claim-5 bound via `condDensity_le_one` + a `Finset.sum_le_sum`
  comparison against the indicator sum, then `Finset.filter_congr`/`Finset.card_filter` to turn the
  `∑ if good then 0 else 1` sum into the bad-selector count.
- `Lemma53/Density.lean` also grew `density_eq_zero_of_empty` (Step 0 of §6: `A` empty ⟹ `h_A ≡ 0`).
- `Lemma53/LemmaA.lean` (§4, formalizing `Lemma52.txt` = Lemma 5.2, **Part I — complete**) —
  `lemmaA`, discharging the `lemmaA` hypothesis `main_lemma` had taken as given. See "Part I"
  below for the full design (an induction avoiding `Lemma52.txt`'s own Gaussian-elimination
  argument, in the same intrinsic-subspace spirit as the Part E design pivot).
- `Lemma53/Lemma53.lean` — the capstone file: `Lemma53.Lemma53` (yes, the theorem is named the
  same as its enclosing namespace — deliberate, since it *is* Lemma 5.3, fully discharged;
  `set_option linter.dupNamespace false in` silences the resulting lint warning) combines
  `main_lemma` (Part H) with `lemmaA` (Part I) into the affine-to-conical decomposition with
  **no hypotheses and no imported facts** at all.

All of the above are fully proved — **zero `sorry`** anywhere in the project.
**The entire formalization (Parts A through I) is complete, including Lemma A.**
`lake build Lemma53` succeeds cleanly with zero warnings, and `Lemma53.Lemma53` is a fully
unconditional theorem (no imported facts, no hypotheses).

## Key design decisions

- Represent an assignment `X : (F₂³)^N` directly as `Fin N → Block` (not pre-split), and only
  introduce the `(s, y)` split in `Selector.lean`, where the paper itself introduces it (§7). Avoids
  ever needing an isomorphism `(F₂³)^N ≃ F₂^N × F₂^{2N}` up front.
- `A` is Mathlib's abstract `AffineSubspace F2 (V N)`, not a hand-rolled matrix system — matches
  §2 ("let `A` be an affine subspace") directly.
- **Part E design pivot** (deviates from Lemma53.txt's own §18 plan, deliberately): §7 informally
  "chooses a full-row-rank system `M_s s + M_y y = c`" representing `A` and defines `L :=
  rowspan(M_y)`. Constructing such a matrix explicitly in Lean (picking bases, proving full row
  rank) is real work for no payoff — every fact §7-16 actually needs about `L` is a *dimension* or
  *support* fact, not the matrix itself. So `L` is instead defined directly and intrinsically:
  `directionAfterFix A := A.direction.comap ιY` (where `ιY : Y N →ₗ V N` is the fixed linear
  embedding `y ↦ (0, y)`, independent of `σ` — this *is* the formal reason §7's own remark "`L`
  does not depend on `σ`" holds), and `L := rowspanL A := dotY.orthogonal (directionAfterFix A)`,
  the orthogonal complement w.r.t. the standard dot-product `BilinForm` on `Y N`. `t ≤ codim A`
  then follows from two rank-nullity arguments (`LinearMap.finrank_range_add_finrank_ker` twice)
  instead of the matrix-existence detour. This is mathematically equivalent to §7's construction
  (`(D')ᗮ` is exactly what `M_y`'s rows would span) but needed zero `sorry`s to set up. The same
  intrinsic style should carry through the rest of Part E (Claim 1) rather than reverting to an
  explicit-matrix approach.
- **Claim 4 design simplification**: Lemma53.txt's §15 states Claim 4 as an *exact* value
  (`Pr_σ[w ∈ E_σ] = 2^{-|bsupp(w)|}` in the nice case, `0` if `w` uses both coordinates of some
  block), proved by a case split on whether `w` uses both coordinates. Only the **upper bound**
  (`≤`) is actually needed downstream (Claim 5's union bound doesn't care about equality), and the
  upper bound holds *uniformly*, no case split required: `w ∈ E_σ` trivially forces `σ i =
  target w i` for every `i ∈ bsupp(w)` regardless of whether `w` is "achievable" by any `σ` at
  all (`mem_E_imp_forced`, proved directly from `w = selSpread σ q` for the specific witnessing
  `σ`, no contradiction/case-split needed) — so `{σ // w ∈ E_σ}` always injects into the
  `card_cube`-counted set, whether or not that set (or the fiber) is actually empty. This is the
  same pattern as Part E's "only prove the `≤` direction, skip the exact value" simplification —
  worth checking for again in Part H if the final bound only needs one direction.
- Cardinalities use `Set.ncard` (and `Nat.card` of subtypes) throughout, not `Fintype.card` with
  manually-supplied `Decidable`/`Fintype` instances. `Set.ncard s = Nat.card ↥s` definitionally
  (`Nat.card_coe_set_eq`), and `Nat.card`/`Nat.card_congr`/`Nat.card_sigma` work classically without
  needing decidability of `AffineSubspace` membership. This paid off cleanly for the
  selector-partition bijection in `Selector.lean`.
- Lemma A (§4, "affine mass bound") is explicitly **out of scope**: Lemma53.txt says it's Lemma 5.2 of
  a separate manuscript. It should enter Part H as a hypothesis/imported fact, not be reproved here.
- Per Lemma53.txt's own closing advice (end of §18): prefer `4 * r > R` / `4 * r ≤ R` case splits over
  `R / 4` nat division; do cardinality/rank arguments in `ℕ`/exact powers of 2 and cast to `ℝ` only
  at the very end. See `density_eq_avg_condDensity` for the pattern: prove the `Nat.card`/`ncard`
  identity first, cast once at the very end via `exact_mod_cast`.

- **`F2 := ZMod 2` needs `instance : Fact (Nat.Prime 2)` registered (in `Gadget.lean`, plus
  `import Mathlib.Algebra.Field.ZMod`) before it is recognized as a `Field`/`DivisionRing`.**
  Without it, `Module.finrank`/`FiniteDimensional`/anything needing `DivisionRing F2` fails —
  and it fails as a **slow `(deterministic) timeout at whnf/isDefEq`, not a clean "instance not
  found" error**, which is very misleading (looks like a performance problem, e.g. a `ZMod`
  instance-diamond issue, and it isn't one). Parts A–D never hit this because they only ever
  used `CommRing`/`Fintype`/`DecidableEq F2`, all unconditionally available for `ZMod n`. If a
  `Module.finrank`/`FiniteDimensional`/`LinearMap.BilinForm` goal times out mysteriously, check
  this instance is in scope before assuming anything else is wrong.
- `LinearMap.BilinForm.orthogonal (B) (N : Submodule) : Submodule` and
  `LinearMap.BilinForm.finrank_orthogonal (hB : B.Nondegenerate) (W) : finrank (B.orthogonal W) = finrank V - finrank W`
  — `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`. `Nondegenerate B := SeparatingLeft B ∧
  SeparatingRight B` (an `And`, not directly `intro`-able — `refine ⟨?_, ?_⟩` first). Building a
  concrete form via `LinearMap.mk₂ F2 f h1 h2 h3 h4` works, but applying it (`(mk₂ ... ) x y`)
  does **not** reduce by `rfl` — need `simp [dotForm]` (or explicitly `LinearMap.mk₂_apply`) to
  unfold. Verified working end-to-end on a hand-rolled dot-product form on `Fin k → F2`.

## Useful Mathlib lemmas found (rediscovering these was slow — reuse, don't re-derive)

- `Equiv.subtypePiEquivPi {p : ∀ a, β a → Prop} : {f : ∀ a, β a // ∀ a, p a (f a)} ≃ ∀ a, {b // p a b}`
  — `Mathlib.Logic.Equiv.Basic`. Turns "N-tuple satisfying a per-index predicate" into a Pi type of
  subtypes (used for gadget fiber ≃ product of single-block fibers).
- `Equiv.subtypeEquivRight (e : ∀ x, p x ↔ q x) : {x // p x} ≃ {x // q x}` — same file.
- `Nat.card_congr : α ≃ β → Nat.card α = Nat.card β` and
  `Nat.card_sigma {β : α → Type*} [Fintype α] [∀ a, Finite (β a)] : Nat.card (Σ a, β a) = ∑ a, Nat.card (β a)`
  — `Mathlib.SetTheory.Cardinal.Finite`.
- `Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard := rfl` and
  `Set.ncard_le_ncard (h : s ⊆ t) (ht : t.Finite) : s.ncard ≤ t.ncard` — `Mathlib.Data.Set.Card`.
- `Finset.sum_div` (the unconditional *field* version) lives in `Mathlib.Algebra.BigOperators.Field`
  — **not** `Mathlib.Algebra.BigOperators.Ring.Finset` (that one is `protected` and needs a
  divisibility hypothesis; easy to grab by mistake and get a confusing error).
- `Module.card_eq_pow_finrank [Fintype K] [Fintype V] : Fintype.card V = Fintype.card K ^ finrank K V`
  — `Mathlib.FieldTheory.Finiteness`. Needed for the solution-counting lemma (Part E): counts a
  finite-dimensional `F2`-vector space via its `finrank`.
- `LinearMap.finrank_range_add_finrank_ker` (rank-nullity) and
  `Matrix.rank A := finrank R (LinearMap.range A.mulVecLin)` — `Mathlib.LinearAlgebra.Matrix.Rank`.
- Module-instance imports needed for `Fin N → F2 × F2 × F2` to be recognized as an `F2`-module:
  `Mathlib.Algebra.Module.Pi` + `Mathlib.Algebra.Module.Prod` (easy to miss — the failure mode is a
  generic "failed to synthesize `Module F2 (V N)`" with no hint about which import is missing).

## Gotchas hit during development

- `fin_cases s <;> simp [gadget]` does **not** close `gadget s u v = (1-s)u+sv` when `u, v` are
  still free variables — `simp` unfolds `gadget` into an `if` but won't reduce/ring-normalize around
  free vars. Fix used: `fin_cases s <;> fin_cases u <;> fin_cases v <;> decide` (fully closed, tiny
  search space).
- `positivity` failed on `0 ≤ (ncard : ℝ) / 4 ^ N`-shaped goals in this project (terse "failed to
  prove positivity/nonnegativity/nonzeroness", no further diagnostic even run directly via
  `lake env lean`). Root cause not pinned down (possibly a missing extension from trimmed imports).
  Workaround used throughout: prove manually via `div_nonneg`, `pow_nonneg`, `pow_pos` with
  `by norm_num` for the numeric base case, instead of reaching for `positivity`.
- An editor-side "minimize imports" pass silently rewrites `import Mathlib.Foo` down to the
  narrowest set it can prove suffices — a file's import list may change underneath you after saving;
  it's not a regression, just re-verify with a build if it happens mid-session.
- `simp` can silently fail to discharge an `if`-condition subgoal even when the exact hypothesis is
  in the simp set (e.g. `simp [cubeIndicator, heq]` left `heq`'s own statement as the unsolved goal,
  and flagged `heq` as an "unused simp arg"). Fix: `unfold cubeIndicator; rw [if_pos heq]` explicitly
  instead of trusting simp to close `if`-conditions from a hypothesis.
- `lake env lean Lemma53/Foo.lean` typechecks against whatever `.olean`s are already on disk for
  its imports — it does **not** rebuild an upstream file whose source changed. If file B imports
  file A and you just edited A, `lake env lean B.lean` can fail with a bogus-looking
  "unknown identifier" for something A clearly defines (autoImplicit then makes the error
  message actively misleading — "unknown identifier, treated as implicit variable, but a
  function was expected" rather than a clean importing error). Fix: run `lake build` (whole
  project, or at least the changed file) before typechecking anything downstream of an edit.
- `sPartitionEquiv` in `Selector.lean` (the `↥S ≃ Σ σ, ↥(combine σ ⁻¹' S)` bijection) has
  `left_inv`/`right_inv` proved by bare `Subtype.ext (combine_split N X)` / `rfl` respectively —
  Lean 4's kernel eta for `Prod`/`Pi` made the `combine`/`split` round trip defeq, which was not
  obvious in advance but avoided a lot of manual `Sigma`/`HEq` wrangling. If similar splitting
  equivalences are needed later (e.g. for `E_σ`/`W_σ`), try bare `rfl` first before writing it out.
- `Submodule.orthogonalBilin`/`LinearMap.BilinForm.orthogonal` membership is
  `m ∈ S.orthogonalBilin B ↔ ∀ n ∈ S, B n m = 0` — **the reference submodule's element comes
  first** in the bilinear form application, the tested element second. Easy to get backwards (I
  did, twice) since it reads naturally the other way round in prose ("m is orthogonal to S").
  Symptom when backwards: a "type mismatch" error showing the two arguments of the `BilinForm`
  application swapped between what a hypothesis has and what the goal wants — fix by inserting a
  `_symm` rewrite (`dotY_symm`/`dotN_symm`) at exactly that point, not by restructuring the proof.
- `rw [← LinearMap.BilinForm.orthogonal_orthogonal hB hB₀]` (or any lemma of shape
  `∀ W, f W = W` used backwards) fails with "pattern to be substituted is a metavariable" if `W`
  is left for Lean to infer from the rewrite target — the target is a *membership* goal
  (`x ∈ W'`), not literally the shape `f ?W`, so unification has nothing to pin `?W` down with.
  Fix: pass `W` **explicitly** as the last argument, e.g.
  `orthogonal_orthogonal hB hB₀ (Submodule.map f D)`, turning the rewrite rule fully concrete
  before `rw` sees it.
- `Finset.sum_congr rfl (fun i _ => ...)` proves two **sums** equal termwise — it does not apply
  to a goal `∑ i, f i = 0` (comparing a sum to a bare constant), even though the tactic state
  doesn't immediately reject it (it fails later with a confusing `AddCommMonoid ?m` "stuck
  typeclass" error at the `fun i _ => ...` binder, not at `Finset.sum_congr` itself). Use
  `Finset.sum_eq_zero (fun i _ => ...)` instead for that shape.
- Hunting for the exact `div_le_div_of_*`/`div_le_div_right` lemma name (they vary across Mathlib
  versions/files) is not worth it for a goal of shape `a/c ≤ b/c` — `gcongr` handles it directly
  (reduces to `a ≤ b`, discharges `0 < c`/`0 ≤ c` itself) and, if the reduced goal `a ≤ b` is
  already a hypothesis in context, `gcongr` closes the whole thing with no further tactic needed
  (calling `exact` afterward then errors "no goals" — check before adding one).
- **`haveI := f` vs `letI := f` for a locally-derived instance (e.g. from `choose`) is not
  interchangeable — this cost ~8 failed rebuilds in `Junta.lean`.** `haveI` is *opaque*: it
  introduces a fresh local constant (shown as `this` in the goal) that later `rfl`/defeq checks
  will **not** unfold back to the original term, even though they're propositionally equal. Two
  proof branches that each independently need `Fintype (ιF k)` — one via the original function
  (`instF k`, e.g. baked into a hypothesis obtained through `choose`), one via typeclass search
  finding the `haveI`-registered copy (`this k`) — end up with *syntactically different* instance
  arguments on otherwise-identical `Finset.univ` terms, and `rfl`/`simp`'s closing check fails with
  no useful error (goal displays as visually identical on both sides — the mismatch is only in the
  invisible instance argument; `#print`/inspecting the raw term is the only way to see it). Fix:
  use `letI := f` instead — `letI` is *transparent* (zeta-reducible), so later defeq checks unfold
  it back to `f` and both branches end up using the same instance term. Rule of thumb: prefer
  `letI` over `haveI` whenever the instance's later uses need to defeq-match something built from
  the original (pre-`haveI`) term, which is the common case when the instance came from `choose`
  rather than being freshly constructed.
- Building a `Fintype`-indexed `Σ` (sigma) sum from a nested double sum (`∑ a, ∑ b, f a b`) is a
  recurring need (combining per-index conical-junta witnesses) — the reliable recipe is
  `rw [← Finset.univ_sigma_univ, Finset.sum_sigma]` (in that order, on the sigma-sum side of the
  goal), **not** `Finset.sum_sigma'` (its `f` argument is curried `∀ a, σ a → β`, not a single
  `Sigma σ → β` argument — easy to reach for by name-similarity and get a confusing "type
  mismatch: `p.snd` expected `ιF ?m`" error instead). `Finset.univ_sigma_univ : Finset.univ.sigma
  (fun _ => Finset.univ) = Finset.univ` bridges `Finset.univ` for the sigma type and
  `Finset.sigma` of two `Finset.univ`s — needed because `Finset.sum_sigma` itself is stated for
  `Finset.sigma`, not `Finset.univ` on a `Σ` type directly. Also: state the Sigma type's binder
  explicitly (`Σ k : ι, ιF k`, not `Σ k, ιF k`) inside a `refine ⟨...⟩` — without it Lean can fail
  to infer `k`'s type from context, producing a spurious universe/application mismatch far from
  the real cause.
- `Finset.mul_sum`/`Finset.sum_mul` (distributing a scalar into/out of a sum) live in
  `Mathlib.Algebra.BigOperators.Ring.Finset` — a plain `Group.Finset.Basic` import (which covers
  `sum_add_distrib` etc.) is not enough; expect "unknown constant" if only the additive-only file
  is imported, and the failure can cascade into unrelated-looking `Finset.sum_congr` type
  mismatches in the same tactic block (the block silently kept operating on the *unrewritten*
  goal once the `simp`/`rw` step referencing the unknown constant failed).
- A `noncomputable def`'s noncomputability is contagious to anything that pattern-matches on or
  case-splits its value, *including* a `Decidable` instance built via `unfold foo; infer_instance`
  when `foo` unfolds to something noncomputable — mark that instance `noncomputable` too, even
  though "is `n ≤ m` decidable" looks like it should always be free.
- **A lambda binder's type must be written explicitly when the body contains a type ascription
  on the bound variable**, e.g. `fun w => ... (w : Y N) ...` inside `(Finset.univ : Finset
  (rowspanL N A)).filter (fun w => ...)` — Lean can infer `w`'s type as `Y N` (from the
  ascription inside the body) *before* looking at the `Finset.univ : Finset (rowspanL N A)` it's
  attached to via dot notation, causing a "Finset ↥(rowspanL N A) expected, got Finset (Y N)"
  mismatch that looks like it's about something else entirely. Fix: `fun w : rowspanL N A => ...`
  — pin the binder type, don't rely on inference from usage.
- `Finset.card_biUnion_le` (plain union bound, no `HEq`/`Sigma` needed) is much easier to reach
  for than a dependent-`Sigma`-type injection when formalizing "every bad case has *some*
  witness, each witness's fiber is bounded" — a `Σ w, {σ // w ∈ E_σ}` injection needs
  `Sigma.mk` equality reasoning (which forces first-component equality "for free" via
  `congrArg Sigma.fst`, but extracting the second component then needs `HEq`); working at the
  `Finset`/`Set` level with `s ⊆ t.biUnion u` avoids all of that. Prefer it whenever the
  downstream use only needs a cardinality bound, not the injection itself.
- `div_le_iff` was renamed `div_le_iff₀` in this Mathlib version (the `GroupWithZero`-generality
  naming convention with a `₀` suffix, seen once before for `div_le_div_right` → `gcongr`
  workaround — this is the same family of renames, worth grepping for the `₀` variant first
  next time before assuming a "well-known" order-field lemma still has its old name).
- When a `have`/goal is stated as `(∑ x ∈ s, f x : ℝ)` where `f x : ℕ`, Lean's elaborator
  distributes the cast to each summand *during elaboration* (`(∑ x ∈ s, (f x : ℝ))`, not
  `((∑ x ∈ s, f x : ℕ) : ℝ)`) — so a subsequent `rw [Nat.cast_sum]` meant to "push the cast in"
  fails with "did not find `↑(∑ ...)`" because the goal was never in the wrapped form to begin
  with. Check the actual goal state (not just what you wrote) before reaching for a cast-pushing
  lemma; it may already be unnecessary.
- Real (`Real.rpow`) exponentiation is unavoidable once a bound genuinely needs a fractional
  exponent — `2^{-R/4}` for a runtime `ℕ` value `R` is *not* an integer power. Lemma53.txt's own
  "avoid nat division, use `4r≤R` not `r≤R/4`" advice governs how to *compare* quantities so far;
  it does not mean the final numeric bound avoids fractions too. Useful `Real.rpow` names found:
  `Real.rpow_natCast` (bridge nat-pow ↔ rpow), `Real.rpow_add`/`Real.rpow_sub` (need `0 < base`),
  `Real.rpow_neg` (needs `0 ≤ base`), `Real.rpow_le_rpow_of_exponent_le` (monotonicity for
  `base ≥ 1`, `@[gcongr]`-tagged). Keep every *nat*-level identity (like `2^(a-b)=2^a/2^b` for
  `b≤a`) in plain `pow`/`Nat` form via `eq_div_iff` + `pow_add` — only reach for `rpow` at the
  exact point a real (non-nat) exponent is unavoidable, not earlier.

## Remaining tasks (Parts E–H)

Note: this session's TaskList/TaskCreate tool disconnected partway through (MCP server dropped) —
items #1–#5 were marked done there (Parts A–D) before it went away; there is no live tracker for
#6-9 anymore, use this file as the source of truth for what's left.

### Part E — linear algebra core (§7, §10–11, §14) — **DONE**

All proved, zero `sorry`, across `LinearAlgebra.lean`, `Orthogonal.lean`, `Claim1.lean`:
1. ~~Choose an explicit full-row-rank matrix system~~ — **skipped**, see "Part E design pivot"
   above. `L`/`t`/`E_σ`/`W_σ` are defined intrinsically from `A.direction` instead.
2. `L := rowspanL A`, `t := t A`; `t_le_codim : t A ≤ codim A`.
3. `E σ`, `W A σ := L ⊓ E σ`, `blockSupport`, `U A σ := ⋃_{w∈W} blockSupport w`.
4. **Solution-counting lemma** (`card_ker_mulVecLin`, `card_solutionSet` in `LinearAlgebra.lean`).
5. Claim 1's **dependency half** — the only thing actually needed downstream (Part F's junta-degree
   bound only needs `DependsOn`, not an exact numeric value — and Lemma53.txt's §18 item 17 itself
   marks the exact-formula version "optional"):
   `condDensity_dependsOn : DependsOn N (U N A σ) (fun z => condDensity N A σ z)`, in `Claim1.lean`.

**Deliberately not done, and not needed**: the exact quantitative value of `condDensity A σ`
(`2^{-(t - dim W_σ)} · indicator`) and the `dim W_σ = t - rank(B_U)` formula. Both are marked
"optional" in Lemma53.txt itself (§18 item 17) and nothing in Parts F–H's own descriptions requires
them — Part F only needs `DependsOn` + `|U_σ| ≤ R`, and Part G's Claims 3–5 are purely about
`L`/`W_σ`/`blockSupport`/`U_σ` combinatorics, not about `condDensity`'s value. If a future step
turns out to need the exact value after all, the proof of `condDensity_dependsOn` already contains
all the pieces (the `d0`-translation bijection argument) — extending it to compute the fiber's
exact cardinality via `card_solutionSet`-style reasoning is the way in.

**Reusable technique for Parts F–H**: the "adjoint pair + orthogonal complement" pattern used
twice now (`ιY`/`splitY` for `L`, `selPick σ`/`selSpread σ` for Claim 1) is: (a) build the two
linear maps and prove them mutually adjoint w.r.t. the relevant `dotY`/`dotN` (a short per-term
`by_cases`/`simp` computation each time); (b) get `(map f D)ᗮ = comap f_adjoint (Dᗮ)` by unfolding
both sides via `Submodule.mem_orthogonalBilin_iff` and `dotN_symm`/`dotY_symm` to swap argument
order (this is where `orthogonalBilin`'s "reference-element-first" argument order, see gotcha
below, actually bites — expect to need `_symm` rewrites at exactly this step); (c) get existence
of witnesses via `LinearMap.BilinForm.orthogonal_orthogonal` (needs `Nondegenerate` + `IsRefl`,
the latter free from symmetry via `fun x y h => (B_symm y x).trans h`) with the target submodule
passed **explicitly** (see gotcha below — `rw [←]` cannot infer it). Claim 3's "half the space"
argument (Part G) will likely want the same nondegeneracy/adjoint toolkit again.

### Part F — `J_A`/`E_A` construction (§12–13) — **DONE**

All proved in `GoodBad.lean` + the three new closure lemmas in `Junta.lean`, zero `sorry`:
7. `good σ := |U_σ| ≤ R`; `J_A`, `E_A` as sums over good/bad `σ` of `condDensity`.
8. `density = J_A + E_A` (`density_eq_J_add_Err`); `0 ≤ J_A ≤ density` (`J_nonneg`,
   `J_le_density`); `E_A ≥ 0` (`Err_nonneg`, not in the original plan but trivial and useful later).
9. `J_A` is a degree-`R` conical junta (`isConicalJunta_J`): each good `condDensity N A σ` is a
   junta via `isConicalJunta_of_dependsOn` + `condDensity_dependsOn`; each bad selector contributes
   the zero junta (`isConicalJunta_zero`); scale each by `2⁻¹^N` (`isConicalJunta_const_mul`);
   combine over all `σ` with `isConicalJunta_sum`.

### Part G — bad-selector estimate (§14–16, Claims 3–5) — **DONE**

All in `Lemma53/BadSelector.lean` (+ `card_cube` in `Junta.lean`), zero `sorry`:
10. ~~A nonzero linear functional on a finite `F2`-vector space is `1` on exactly half the
    space~~ — proved generically as `card_functional_eq_one` in `LinearAlgebra.lean` (reusable
    beyond this specific application).
11. Claim 3, proved as `exists_wide_of_card_U_gt`, via a **division-free** route that deviates
    from Lemma53.txt's own expectation-based argument: the exact identity
    `sum_blockSupport_eq` (`2·Σ|bsupp w| = |U_σ|·|W_σ|`) plus a direct sum-bound contradiction,
    rather than "average exceeds threshold ⟹ some element exceeds it". No real numbers, no
    `R / 2` anywhere.
12. Claim 4, proved as `card_sigma_mem_E_le` (upper bound only — see design note above):
    `Nat.card {σ // w ∈ E_σ} ≤ 2 ^ (N - |bsupp(w)|)` for **any** `w : Y N`, no case split on
    "uses both coordinates" needed. Key lemma: `mem_E_imp_forced` (`w ∈ E_σ` forces `σ = target w`
    on `bsupp(w)`), then inject `{σ // w ∈ E_σ} ↪ {z // ∀i∈bsupp w, z i = target w i}` and apply
    `card_cube`.
13. Claim 5: `card_bad_le_sum` gets the nat/`Finset` union bound over `w ∈ L` via
    `Finset.card_biUnion_le` (much simpler than a dependent-`Sigma`-type injection — avoids
    `HEq` entirely, see gotcha below), then `card_bad_le_real` converts to the real bound
    `Nat.card {σ // R < |U_σ|} ≤ 2^N · 2^{-R/4}` given `4 * t N A ≤ R`, via `Real.rpow`
    (`term_le` bounds each summand by `2^N·2^{-R/2}` using `two_pow_sub_eq` — a *nat*-power
    identity `2^(a-b)=2^a/2^b`, no rpow needed there — then `Real.rpow_le_rpow_of_exponent_le`
    for the cross term, and `t ≤ R/4` combined with `t_le_codim` for the final `2^{R/4}` factor).
    The very last algebraic step turned out to be an *equality*, not a further inequality:
    `2^{R/4}·2^{-R/2} = 2^{-R/4}` exactly, via `Real.rpow_add`.

### Part H — final assembly (§6, §17) — **DONE**

All in `Lemma53/MainLemma.lean` (+ `condDensity_le_one` in `Claim1.lean`, `Err_le_real` in
`BadSelector.lean`, `density_eq_zero_of_empty` in `Density.lean`), zero `sorry`:
14. Lemma A (§4, affine mass bound) taken as an imported **hypothesis** parameter of `main_lemma` —
    Lemma 5.2 of a separate manuscript, explicitly out of scope here.
15. Three-way case split: `A` empty (Step 0) / `A` nonempty with `4·codim A > R` (Step 1, Lemma A
    directly) / `A` nonempty with `4·codim A ≤ R` (Parts E–G, `Err_le_real` + Claim 5).
16. Combined into `main_lemma` with `κ = min(κ₀/4, 1/4)`.

### Part I — Lemma A (§4, "affine mass bound", = `Lemma52.txt` = Lemma 5.2) — **DONE**

All proved in `Lemma53/LemmaA.lean`, zero `sorry`. Discharges the `lemmaA` hypothesis Part H
(`main_lemma`) takes as given; `Lemma53/Lemma53.lean` then combines it with `main_lemma` into
`Lemma53.Lemma53` — the affine-to-conical decomposition with **no hypotheses at all**.
Target statement (exactly matches `main_lemma`'s hypothesis shape): `lemmaA : ∀ (A : AffineSubspace
F2 (V N)), (A : Set (V N)).Nonempty → ∀ z, density N A z ≤ (2:ℝ) ^ (-κ0 * (codim N A : ℝ))`, with
`κ0 := (1/3) * Real.logb 2 (4/3)` and `κ0_pos : 0 < κ0`.

**Design pivot from `Lemma52.txt`'s own proof sketch** (same spirit as the Part E design pivot
above). `Lemma52.txt`'s proof performs explicit Gaussian elimination on a chosen full-rank matrix
`M` representing `A`, picks pivot rows/columns block-by-block, and processes blocks "right to
left" with previously-fixed values. Since (as with Part E) every fact actually needed about `A` is
a *dimension* fact about `A.direction`, not the matrix itself, this instead proves the same bound
(`|A ∩ Fib(z)| ≤ 3^m · 4^{N-m}` with `codim A ≤ 3m`) by **induction on `N`, peeling off one
gadget-block coordinate at a time via rank-nullity**, entirely avoiding Gaussian
elimination/pivoting:
- Work with `D := A.direction` (a `Submodule F2 (V N)`) and a basepoint `x0 ∈ A`, using
  `coe_eq_vadd_direction : (A : Set (V N)) = x0 +ᵥ (D : Set (V N))` (via Mathlib's
  `AffineSubspace.vadd_mem_iff_mem_direction`) so the induction (`coset_inter_gadgetFiber_bound`)
  is stated purely in terms of a **coset of a submodule**, never touching
  `AffineSubspace.map`/`AffineMap` machinery.
- `headLM n : V (n+1) →ₗ[F2] Block := LinearMap.proj 0` and
  `tailLM n : V (n+1) →ₗ[F2] V n := LinearMap.pi (fun i : Fin n => LinearMap.proj i.succ)` split
  off the first block; `ker_head_inf_ker_tail : ker head ⊓ ker tail = ⊥` (a tuple is determined by
  its head and tail).
- One reusable generic lemma (added to `LinearAlgebra.lean`, same style as `card_solutionSet`/
  `card_functional_eq_one`): `finrank_map_add_finrank_inf_ker`, for `f : M →ₗ[F2] N` and
  `p : Submodule F2 M`: `finrank (p.map f) + finrank (p ⊓ ker f) = finrank p` (proved via
  `f.comp p.subtype`, `LinearMap.range_comp`/`Submodule.range_subtype` for the range half,
  `Submodule.finrank_map_subtype_eq` + `Submodule.map_comap_subtype` for the kernel half, then
  `LinearMap.finrank_range_add_finrank_ker` on the restricted map). Applied twice per induction
  step: once with `f := tailLM n` on `D` (splits off `D' := D.map tailLM`, the "rest" direction),
  once with `f := headLM n` on `Dk := D ⊓ ker tailLM` (splits off `D'' := Dk.map headLM`, the
  "vertical, head-only" part of the direction) — combined with `ker_head_inf_ker_tail`, this gives
  `finrank D'' = finrank Dk` directly (`hkerinf`), so overall `finrank D = finrank D' + finrank D''`
  exactly, unconditionally (no case split needed for this identity).
- **Simplification found during implementation, beyond the original plan**: the original plan
  called for a genuine bijection in the `D'' = ⊤` case (exact `×4`) versus an injection in the
  `D'' ≠ ⊤` case (`≤ 3×`). This turned out to be unnecessary — **both cases reduce to the same
  uniform fiber-counting argument**. For *any* `D''` (top or not), the fiber of `X ↦ tailLM n X`
  over a fixed `Y` injects into `Block` via `headLM n` (since `ker head ⊓ ker tail = ⊥`), and that
  image is *always* a subset of the single-block fiber `{t | blockEval t = z 0}` (`≤ 4` points,
  trivially, since that set simply has `4` elements — `blockFiber_ncard`) — no need for `D''` at
  all for this bound. *Only* the tighter `≤ 3` bound (used when `D'' ≠ ⊤`, to make `m` actually
  grow) needs `D''`: the image is additionally inside a coset of `D''`
  (`hcoset : headLM n X1 - headLM n X2 ∈ D''` whenever `tailLM n X1 = tailLM n X2`, both in the
  coset `x0 +ᵥ D`), and `coset_fiber_le_three` (below) bounds that by `3`. Both bounds are pushed
  through one shared helper, `ncard_le_mul_ncard_image` (a `Set.ncard` version of the
  "bounded-fiber ⟹ bounded total" pigeonhole lemma, via `Finset.card_le_mul_card_image_of_maps_to`
  in `Mathlib.Algebra.Order.BigOperators.Group.Finset`, bridged through `Set.Finite.toFinset`).
  Case split is still needed for choosing `m := m'` (the `D'' = ⊤` branch, `×4` factor) vs.
  `m := m' + 1` (the `D'' ≠ ⊤` branch, `×3` factor) — but *not* for constructing the set-level
  argument itself. Worth checking for this "one proof, two applications" pattern again if a
  future part seems to need a case-split bijection/injection.
- **Local fact** (`fiber_affine_le_three`): a nonconstant affine equation `dot a t = d` on `Block`
  is satisfied by `≤ 3` of the `4` points of any `{t | blockEval t = b}`, proved by `decide` over
  `Block`'s `8` elements (`fin_cases a <;> try exact absurd rfl ha; all_goals fin_cases b <;>
  fin_cases d <;> decide`). Getting from "`D'' ≠ ⊤`" to a concrete nonconstant equation
  (`exists_dot_ne_zero_of_ne_top`) needs a small `dotBlock` nondegenerate `BilinForm` on `Block`
  (built exactly like `dotY`/`dotN` in `Orthogonal.lean`/`Claim1.lean` — the "adjoint pair +
  orthogonal complement" toolkit CLAUDE.md already flagged as reusable): `D''ᗮ ≠ ⊥` since
  `D'' ≠ ⊤` (via `Submodule.finrank_lt_finrank_of_lt` + `LinearMap.BilinForm.finrank_orthogonal`),
  any nonzero `a ∈ D''ᗮ` gives the nonconstant functional (`coset_fiber_le_three`).
- Base case `N = 0`: `V 0 = (Fin 0 → Block)` has exactly one element (`Fintype.card_pi` over the
  empty index `Fin 0`, an empty product `= 1`); `m := 0` closes it immediately.
- Final numeric step (only place needing `Real.rpow`, same as Claim 5/Part H): converts
  `codim A ≤ 3m ∧ ncard·4^m ≤ 3^m·4^N` (all-`ℕ`, via `lemmaA_nat`) into
  `density A z ≤ (3/4)^{codim A / 3} = 2^{-κ0·codim A}`, casting to `ℝ` only at this last step
  (per `Lemma53.txt`/CLAUDE.md's own established convention). The `(3/4)^x = 2^{-κ0·3x}` identity
  (`rpow_three_quarter_eq`) goes through `Real.rpow_mul`/`Real.rpow_logb`/`Real.rpow_neg`/
  `Real.inv_rpow`, using `κ0`'s definition via `Real.logb` exactly so this identity is clean; the
  monotonicity step uses `Real.rpow_le_rpow_of_exponent_ge` (base `≤ 1`: *larger* exponent ⟹
  *smaller* value, the mirror image of the `Real.rpow_le_rpow_of_exponent_le` already used in
  Part H for a base `> 1`).
- **`open scoped Pointwise` is required** for `x0 +ᵥ (D : Set _)` (a single vector translating a
  set) to elaborate at all — the `VAdd (V N) (Set (V N))` instance is `scoped` to the `Pointwise`
  namespace (`Mathlib.Algebra.Group.Pointwise.Set.Scalar`); without the `open`, Lean reports a
  bare `failed to synthesize HVAdd (V N) (Set (V N)) ?m` with no hint that scoping is the issue.

**Files**: `Lemma53/LemmaA.lean` (local fact, `dotBlock`, `headLM`/`tailLM`, the induction, final
numeric bound — `lemmaA`, `κ0`, `κ0_pos`), plus `finrank_map_add_finrank_inf_ker` added to
`Lemma53/LinearAlgebra.lean`. The capstone combining `lemmaA` with `main_lemma` lives in its own
file, `Lemma53/Lemma53.lean` (theorem `Lemma53.Lemma53`), added to the root `Lemma53.lean` import
list.

## Next step when resuming

**Parts A–I are all complete — zero `sorry` anywhere, `lake build Lemma53` succeeds with zero
warnings.** There is no required next step; the formalization is done, including Lemma A
(Part I), so `Lemma53.Lemma53` (`Lemma53/Lemma53.lean`) is the final, fully unconditional
theorem — no hypotheses, no imported facts. `#print axioms Lemma53.Lemma53` (and
`Lemma53.lemmaA`) show only the standard `Classical.choice`/`Quot.sound`/`propext` trio, confirming
no hidden `sorry`-equivalent anywhere in the dependency chain. `Lemma53_axcheck_temp.lean` is a
standing scratch file that runs all three axiom checks (`main_lemma`, `lemmaA`,
`Lemma53.Lemma53`) — rerun it (`lake env lean Lemma53_axcheck_temp.lean`) after any future
edit to re-verify.
