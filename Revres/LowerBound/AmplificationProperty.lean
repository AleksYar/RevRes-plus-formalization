import Revres.LowerBound.RobustIdentity
import Revres.Conical.Representation

/-!
# Abstract robust amplification property

This file isolates the semantic input that the later preprocessing and amplification development
must provide.  It is stated on explicit conical-junta representations so those later arguments can
inspect and transform individual terms.
-/

namespace Revres

variable {N : ℕ}

/-- A robust identity with a nonnegative degree-bounded junta must attain `growth` whenever its
error is pointwise bounded by `errorCap`. -/
def RobustAmplificationProperty
    (F : CNF N)
    (degree : ℕ)
    (errorCap growth : ℝ) : Prop :=
  ∀ (P E : (Fin N → Lemma53.F2) → ℝ) (JR : JuntaRep N),
    HasNonnegativeAxiomRepresentation F P →
    JR.Nonnegative →
    JR.DegreeLE degree →
    (∀ z, P z = 1 + JR.eval z + E z) →
    (∀ z, 0 ≤ E z ∧ E z ≤ errorCap) →
    ∃ z, growth ≤ JR.eval z

end Revres
