import Revres.Conical.Term
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite completion of canonical terms

A term can be completed on a finite coordinate set by enumerating assignments only on the
coordinates not already fixed.  The resulting indicators partition the original indicator.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace Term

variable {N : ℕ}

/-- Coordinates in `S` on which `t` does not yet impose a value. -/
def missingOn (t : Term N) (S : Finset (Fin N)) : Finset (Fin N) :=
  S \ t.support

/-- Extend `t` by one assignment on exactly the coordinates missing from `S`. -/
def fillOn (t : Term N) (S : Finset (Fin N))
    (a : ↑(t.missingOn S) → F2) : Term N where
  val i := if hi : i ∈ t.missingOn S then some (a ⟨i, hi⟩) else t.val i

theorem fillOn_extends (t : Term N) (S : Finset (Fin N))
    (a : ↑(t.missingOn S) → F2) {i : Fin N} {b : F2}
    (hib : t.val i = some b) :
    (t.fillOn S a).val i = some b := by
  have hi : i ∈ t.support := by simp [hib]
  have hmissing : i ∉ t.missingOn S := by simp [missingOn, hi]
  simp [fillOn, hmissing, hib]

@[simp]
theorem support_fillOn (t : Term N) (S : Finset (Fin N))
    (a : ↑(t.missingOn S) → F2) :
    (t.fillOn S a).support = t.support ∪ S := by
  ext i
  by_cases hit : i ∈ t.support
  · have hmissing : i ∉ t.missingOn S := by simp [missingOn, hit]
    have hval : t.val i ≠ none := Term.mem_support.mp hit
    simp [Term.mem_support, fillOn, hmissing, hit, hval]
  · by_cases hiS : i ∈ S
    · have hmissing : i ∈ t.missingOn S := by simp [missingOn, hit, hiS]
      simp [Term.mem_support, fillOn, hmissing, hit, hiS]
    · have hmissing : i ∉ t.missingOn S := by simp [missingOn, hiS]
      have hval : t.val i = none := Term.not_mem_support.mp hit
      simp [Term.mem_support, fillOn, hmissing, hit, hiS, hval]

theorem fillOn_injective (t : Term N) (S : Finset (Fin N)) :
    Function.Injective (t.fillOn S) := by
  intro a c hac
  funext i
  have hi := i.property
  have hval := congrArg (fun u : Term N => u.val i.1) hac
  simpa [fillOn, hi] using hval

/-- All distinct extensions of `t` that fix every coordinate in `S`. -/
noncomputable def completeOn (t : Term N) (S : Finset (Fin N)) : Finset (Term N) := by
  classical
  exact Finset.univ.image (t.fillOn S)

theorem mem_completeOn_iff {t : Term N} {S : Finset (Fin N)} {u : Term N} :
    u ∈ t.completeOn S ↔ ∃ a : ↑(t.missingOn S) → F2, t.fillOn S a = u := by
  classical
  simp [completeOn]

theorem support_eq_of_mem_completeOn {t : Term N} {S : Finset (Fin N)} {u : Term N}
    (hu : u ∈ t.completeOn S) :
    u.support = t.support ∪ S := by
  obtain ⟨a, rfl⟩ := mem_completeOn_iff.mp hu
  exact support_fillOn t S a

theorem degree_eq_of_mem_completeOn {t : Term N} {S : Finset (Fin N)} {u : Term N}
    (hu : u ∈ t.completeOn S) :
    u.degree = (t.support ∪ S).card := by
  rw [Term.degree, support_eq_of_mem_completeOn hu]

theorem degree_le_of_mem_completeOn {t : Term N} {S : Finset (Fin N)} {u : Term N}
    (hu : u ∈ t.completeOn S) :
    u.degree ≤ t.degree + S.card := by
  rw [degree_eq_of_mem_completeOn hu, Term.degree]
  exact Finset.card_union_le (s := t.support) (t := S)

theorem card_completeOn (t : Term N) (S : Finset (Fin N)) :
    (t.completeOn S).card = 2 ^ (t.missingOn S).card := by
  classical
  rw [completeOn, Finset.card_image_of_injective _ (fillOn_injective t S),
    Finset.card_univ, Fintype.card_fun]
  simp [ZMod.card]

theorem matches_of_mem_completeOn {t : Term N} {S : Finset (Fin N)} {u : Term N}
    {z : Fin N → F2} (hu : u ∈ t.completeOn S) (huz : u.Matches z) :
    t.Matches z := by
  intro i b hib
  exact huz i b (by
    obtain ⟨a, rfl⟩ := mem_completeOn_iff.mp hu
    exact fillOn_extends t S a hib)

private theorem fillOn_matches_completion
    (t : Term N) (S : Finset (Fin N)) (z : Fin N → F2)
    (htz : t.Matches z) :
    (t.fillOn S fun i => z i.1).Matches z := by
  intro i b hib
  by_cases hi : i ∈ t.missingOn S
  · simpa [fillOn, hi] using hib
  · have htib : t.val i = some b := by simpa [fillOn, hi] using hib
    exact htz i b htib

theorem existsUnique_mem_completeOn_matches
    (t : Term N) (S : Finset (Fin N)) (z : Fin N → F2)
    (htz : t.Matches z) :
    ∃! u : Term N, u ∈ t.completeOn S ∧ u.Matches z := by
  let a : ↑(t.missingOn S) → F2 := fun i => z i.1
  refine ⟨t.fillOn S a, ⟨?_, fillOn_matches_completion t S z htz⟩, ?_⟩
  · exact mem_completeOn_iff.mpr ⟨a, rfl⟩
  · intro u hu
    obtain ⟨c, rfl⟩ := mem_completeOn_iff.mp hu.1
    apply congrArg (t.fillOn S)
    funext i
    have hmatch := hu.2 i.1 (c i) (by simp [fillOn, i.property])
    exact hmatch.symm

theorem sum_indicator_completeOn
    (t : Term N) (S : Finset (Fin N)) (z : Fin N → F2) :
    (∑ u ∈ t.completeOn S, u.indicator z) = t.indicator z := by
  classical
  by_cases htz : t.Matches z
  · obtain ⟨u, hu, hunique⟩ := t.existsUnique_mem_completeOn_matches S z htz
    rw [Finset.sum_eq_single u]
    · simp [Term.indicator, hu.2, htz]
    · intro v hv hne
      have hvnot : ¬v.Matches z := by
        intro hvz
        exact hne (hunique v ⟨hv, hvz⟩)
      simp [Term.indicator, hvnot]
    · exact fun hnot => (hnot hu.1).elim
  · have hnone : ∀ u ∈ t.completeOn S, ¬u.Matches z := by
      intro u hu huz
      exact htz (matches_of_mem_completeOn hu huz)
    rw [Term.indicator, if_neg htz]
    apply Finset.sum_eq_zero
    intro u hu
    rw [Term.indicator, if_neg (hnone u hu)]

end Term

end Revres
