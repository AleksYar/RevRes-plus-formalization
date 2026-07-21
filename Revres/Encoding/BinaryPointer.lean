import Revres.DecisionTree.Read
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact binary pointer codes

For grid order `2 ^ ell - 1`, the `2 ^ ell` bit vectors encode exactly one null value and every grid
column. A normalized finite equivalence makes the all-zero vector precisely the null code.
-/

namespace Revres

open Lemma53

namespace BinaryPointer

/-- Grid order represented by `ell` pointer bits with one code reserved for null. -/
def order (ell : ℕ) : ℕ :=
  2 ^ ell - 1

/-- An `ell`-bit pointer code. -/
abbrev Bits (ell : ℕ) := Fin ell → F2

/-- The distinguished all-zero null code. -/
def nullBits (ell : ℕ) : Bits ell :=
  fun _ => 0

theorem order_pos {ell : ℕ} (hell : 0 < ell) : 0 < order ell := by
  unfold order
  have hpow : 1 < (2 : ℕ) ^ ell :=
    one_lt_pow₀ (by decide) (Nat.ne_of_gt hell)
  exact Nat.sub_pos_of_lt hpow

theorem order_add_one (ell : ℕ) : order ell + 1 = 2 ^ ell := by
  unfold order
  exact Nat.sub_add_cancel (one_le_pow₀ (by decide))

private theorem card_bits (ell : ℕ) : Fintype.card (Bits ell) = 2 ^ ell := by
  rw [Fintype.card_pi_const]
  rw [ZMod.card]

/-- An arbitrary finite enumeration of bit vectors. -/
noncomputable def rawFinEquiv (ell : ℕ) : Bits ell ≃ Fin (2 ^ ell) :=
  Fintype.equivFinOfCardEq (card_bits ell)

/-- The enumeration normalized to send the all-zero vector to finite index zero. -/
noncomputable def normalizedFinEquiv (ell : ℕ) : Bits ell ≃ Fin (2 ^ ell) :=
  (rawFinEquiv ell).trans (Equiv.swap (rawFinEquiv ell (nullBits ell)) 0)

@[simp]
theorem normalizedFinEquiv_nullBits (ell : ℕ) :
    normalizedFinEquiv ell (nullBits ell) = 0 := by
  simp [normalizedFinEquiv]

/-- Exact equivalence between bit vectors and nullable grid columns. -/
noncomputable def pointerEquiv (ell : ℕ) :
    Bits ell ≃ Option (Fin (order ell)) :=
  (normalizedFinEquiv ell).trans
    ((finCongr (order_add_one ell)).symm.trans (finSuccEquiv (order ell)))

/-- Decode a bit vector as a nullable grid column. -/
noncomputable def decode {ell : ℕ} (bits : Bits ell) : Option (Fin (order ell)) :=
  pointerEquiv ell bits

/-- Encode a nullable grid column as its unique bit vector. -/
noncomputable def encode {ell : ℕ} (pointer : Option (Fin (order ell))) : Bits ell :=
  (pointerEquiv ell).symm pointer

@[simp]
theorem decode_nullBits (ell : ℕ) : decode (nullBits ell) = none := by
  simp [decode, pointerEquiv]

@[simp]
theorem encode_none (ell : ℕ) : encode (ell := ell) none = nullBits ell := by
  apply (pointerEquiv ell).injective
  calc
    pointerEquiv ell (encode none) = none := (pointerEquiv ell).apply_symm_apply none
    _ = pointerEquiv ell (nullBits ell) := by
      simpa [decode] using (decode_nullBits ell).symm

theorem decode_eq_none_iff {ell : ℕ} {bits : Bits ell} :
    decode bits = none ↔ bits = nullBits ell := by
  constructor
  · intro hdecode
    apply (pointerEquiv ell).injective
    calc
      pointerEquiv ell bits = none := hdecode
      _ = pointerEquiv ell (nullBits ell) := by
        simpa [decode] using (decode_nullBits ell).symm
  · rintro rfl
    exact decode_nullBits ell

@[simp]
theorem decode_encode {ell : ℕ} (pointer : Option (Fin (order ell))) :
    decode (encode pointer) = pointer :=
  (pointerEquiv ell).apply_symm_apply pointer

@[simp]
theorem encode_decode {ell : ℕ} (bits : Bits ell) :
    encode (decode bits) = bits :=
  (pointerEquiv ell).symm_apply_apply bits

theorem decode_ne_none_iff {ell : ℕ} {bits : Bits ell} :
    decode bits ≠ none ↔ bits ≠ nullBits ell :=
  not_congr decode_eq_none_iff

/-- Read and decode one pointer stored at the supplied assignment coordinates. -/
noncomputable def read {N ell : ℕ} (index : Fin ell → Fin N) :
    DecisionTree N (Option (Fin (order ell))) :=
  (DecisionTree.readTuple index).map decode

@[simp]
theorem eval_read {N ell : ℕ} (index : Fin ell → Fin N) (x : Fin N → F2) :
    (read index).eval x = decode (fun b => x (index b)) := by
  simp [read]

@[simp]
theorem depth_read {N ell : ℕ} (index : Fin ell → Fin N) :
    (read index).depth = ell := by
  simp [read]

end BinaryPointer

end Revres
