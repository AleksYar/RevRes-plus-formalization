import Revres.Polynomial.Certificate
import Revres.SoPL.Encoding
import Revres.SoPL.PathFamily

/-!
# External path-family Nullstellensatz hardness interface

The published support-local SoPL lower bound is represented by an explicit
proposition. Later results thread a proof of this proposition as a hypothesis;
this module does not assert the external theorem.
-/

namespace Revres

open Lemma53

namespace SoPL

/-- An encoded SoPL assignment whose decoded input belongs to the hard path family. -/
def IsEncodedPathFamily (ell : ℕ) (hell : 0 < ell)
    (y : Fin (Encoding.variableCount ell) → F2) : Prop :=
  IsPathFamily (BinaryPointer.order_pos hell) (Encoding.decodeInput ell y)

/-- The support-local approximate-NS lower bound used by amplification. -/
def PathFamilyNSHardness (ell : ℕ) (hell : 0 < ell)
    (degreeLowerBound : ℕ) : Prop :=
  ∀ (Q : (Fin (Encoding.variableCount ell) → F2) → ℝ)
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q),
    (∀ y, IsEncodedPathFamily ell hell y →
      (1 / 2 : ℝ) ≤ Q y ∧ Q y ≤ (3 / 2 : ℝ)) →
    degreeLowerBound ≤ cert.degree

namespace PathFamilyNSHardness

theorem not_approximate_of_degree_lt
    {ell degreeLowerBound : ℕ} {hell : 0 < ell}
    (hHard : PathFamilyNSHardness ell hell degreeLowerBound)
    {Q : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (cert : NSCertificate (Encoding.searchCNF ell hell) Q)
    (hdegree : cert.degree < degreeLowerBound) :
    ¬∀ y, IsEncodedPathFamily ell hell y →
      (1 / 2 : ℝ) ≤ Q y ∧ Q y ≤ (3 / 2 : ℝ) := by
  intro happrox
  exact (Nat.not_le_of_gt hdegree) (hHard Q cert happrox)

end PathFamilyNSHardness

end SoPL

end Revres
