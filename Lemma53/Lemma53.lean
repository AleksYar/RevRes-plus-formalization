import Lemma53.LemmaA
import Lemma53.MainLemma

/-!
# The Main Lemma, unconditionally

Combines Part H (`main_lemma`, which takes Lemma A as a hypothesis parameter) with Part I
(`lemmaA`, the proof of Lemma A) into a single theorem with **no remaining hypotheses**: the
affine-to-conical decomposition of `Lemma53.txt`, fully discharged.
-/

namespace Lemma53

set_option linter.dupNamespace false in
/--
Paper correspondence: Section `sec:indexing-lift`, Lemma
`lem:affine-conical`, equations `eq:decomp` and `eq:error` in
`revres_xor_superpoly_lower_bound_restriction_notation.tex`; the standalone
mathematical source is `Lemma53.txt`.

Mathematical content: Every affine subspace of `(F₂³)^N` has a gadget-fiber
density equal to a degree-`R` conical junta plus a nonnegative error bounded by
`2^(-min (κ₀ / 4) (1 / 4) * R)`.

Formalization note: This unconditional capstone discharges the auxiliary
high-rank input internally through `Lemma53.lemmaA`; it is not an assumed axiom.

Used by: `Revres.finalDensitySum_decomposition` and the robust-identity layer.
-/
theorem Lemma53 (N R : ℕ) (A : AffineSubspace F2 (V N)) :
    ∃ J E : (Fin N → F2) → ℝ,
      (∀ z, density N A z = J z + E z) ∧
      IsConicalJunta N R J ∧
      (∀ z, 0 ≤ J z ∧ J z ≤ density N A z ∧ density N A z ≤ 1) ∧
      (∀ z, 0 ≤ E z ∧ E z ≤ (2 : ℝ) ^ (-(min (κ0 / 4) (1 / 4)) * (R : ℝ))) :=
  main_lemma N κ0 κ0_pos (fun A hA z => lemmaA N A hA z) R A

end Lemma53
