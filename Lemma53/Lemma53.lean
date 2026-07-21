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
/-- **The Main Lemma** (`Lemma53.txt`), unconditionally. Every affine subspace `A ⊆ (F₂³)^N` and
every `R` admit a degree-`R` conical junta `J_A` and an error `E_A` with `h_A = J_A + E_A`,
`0 ≤ J_A ≤ h_A ≤ 1`, and `0 ≤ E_A ≤ 2^{-κR}` for `κ = min(κ₀/4, 1/4)` — no hypotheses, no imported
facts. -/
theorem Lemma53 (N R : ℕ) (A : AffineSubspace F2 (V N)) :
    ∃ J E : (Fin N → F2) → ℝ,
      (∀ z, density N A z = J z + E z) ∧
      IsConicalJunta N R J ∧
      (∀ z, 0 ≤ J z ∧ J z ≤ density N A z ∧ density N A z ≤ 1) ∧
      (∀ z, 0 ≤ E z ∧ E z ≤ (2 : ℝ) ^ (-(min (κ0 / 4) (1 / 4)) * (R : ℝ))) :=
  main_lemma N κ0 κ0_pos (fun A hA z => lemmaA N A hA z) R A

end Lemma53
