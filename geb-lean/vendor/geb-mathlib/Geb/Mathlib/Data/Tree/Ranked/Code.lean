/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.Tree.Ranked.Basic
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# Symbol codes

The block spelling a symbol of a ranked alphabet: its index in binary, least
significant bit first, padded to the alphabet's width. A block decodes to the
symbol it spells, which is what makes the padding lossless, and a block
denoting no symbol has no arity.

## Main definitions

* `RankedAlphabet.code` — the block spelling a symbol.
* `RankedAlphabet.decodeBits` — the value a block denotes.
* `RankedAlphabet.arOf` — the arity of the symbol a block denotes.

## Main statements

* `RankedAlphabet.length_code` — every block has the alphabet's width.
* `RankedAlphabet.decodeBits_code` — a block decodes to its own symbol.
* `RankedAlphabet.arOf_decodeBits_code` — and so has that symbol's arity.
* `RankedAlphabet.testBit_decodeBits` — a block's entries are its value's
  bits.
* `RankedAlphabet.getElem_code_eq` — and a block's entries are the bits of
  the symbol's index.
* `RankedAlphabet.le_maxArity_of_arOf_eq_some` — an arity a block yields is at
  most the largest.

## Implementation notes

`decodeBits` is a bare `List.rec`, so Lean generates no equation lemma for
it; `decodeBits_cons` is stated for the rewrites that need one.

`mod_two_mul` is stated here rather than taken from `Nat`'s division API:
`Nat.mod_mul` states the same identity and depends on `Classical.choice`,
which the axiom linter rejects for this module, and its modulus is a
variable, so `omega` cannot discharge the identity directly. The proof
below runs through `Nat.div_add_mod`, `Nat.mul_add_mod` and
`Nat.mod_eq_of_lt`, all of which are choice-free.

## Tags

ranked alphabet, code, binary representation, decoding
-/

namespace RankedAlphabet

public section

/-- The block spelling a symbol: its index in binary, least significant bit
first, padded to the alphabet's width. -/
@[expose] def code (R : RankedAlphabet) (i : Fin R.card) : List Bool :=
  (List.range R.width).map fun j ↦ i.val.testBit j

/-- The value a block denotes, its head the least significant bit. -/
@[expose] def decodeBits : List Bool → ℕ :=
  List.rec 0 fun b _ ih ↦ 2 * ih + (if b then 1 else 0)

/-- `decodeBits` unfolded on a non-empty block. `decodeBits` is a bare
`List.rec`, for which Lean generates no equation lemma. -/
theorem decodeBits_cons (b : Bool) (l : List Bool) :
    decodeBits (b :: l) = 2 * decodeBits l + (if b then 1 else 0) := rfl

/-- The arity of the symbol a block denotes, absent at a block denoting
none. -/
@[expose] def arOf (R : RankedAlphabet) (v : ℕ) : Option ℕ :=
  if h : v < R.card then some (R.arity ⟨v, h⟩) else none

/-- Every block has the alphabet's width. -/
@[simp] theorem length_code (R : RankedAlphabet) (i : Fin R.card) :
    (R.code i).length = R.width := by
  simp only [code, List.length_map, List.length_range]

/-- Splitting a residue by a factor of two, choice-free. -/
theorem mod_two_mul (v m : ℕ) (hm : 0 < m) :
    v % (2 * m) = 2 * (v / 2 % m) + v % 2 := by
  have h2 : (0 : ℕ) < 2 := by omega
  have hlt1 : v / 2 % m < m := Nat.mod_lt _ hm
  have hlt2 : v % 2 < 2 := Nat.mod_lt _ h2
  conv_lhs => rw [← Nat.div_add_mod v 2, ← Nat.div_add_mod (v / 2) m]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- A block decodes to the symbol it spells. The bound `i.val < 2 ^ width`
comes from `card_le_two_pow_width`, and is what makes the padding
lossless. -/
theorem decodeBits_code (R : RankedAlphabet) (i : Fin R.card) :
    decodeBits (R.code i) = i.val := by
  have hlt : i.val < 2 ^ R.width :=
    Nat.lt_of_lt_of_le i.isLt R.card_le_two_pow_width
  have key : ∀ (n : ℕ) (v : ℕ),
      decodeBits ((List.range n).map fun j ↦ v.testBit j) = v % 2 ^ n := by
    refine Nat.rec (motive := fun n ↦ ∀ v : ℕ,
        decodeBits ((List.range n).map fun j ↦ v.testBit j) = v % 2 ^ n)
      (fun v ↦ by
        simp only [List.range_zero, List.map_nil, decodeBits, Nat.pow_zero, Nat.mod_one])
      (fun n ihn v ↦ ?_)
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Function.comp_def, Nat.succ_eq_add_one, Nat.testBit_add_one]
    rw [decodeBits_cons, ihn (v / 2), Nat.testBit_zero, pow_succ',
      mod_two_mul _ _ (Nat.two_pow_pos n)]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h, Nat.add_comm]
  rw [code, key, Nat.mod_eq_of_lt hlt]

/-- A block spelling a symbol has that symbol's arity. -/
theorem arOf_decodeBits_code (R : RankedAlphabet) (i : Fin R.card) :
    R.arOf (decodeBits (R.code i)) = some (R.arity i) := by
  rw [decodeBits_code, arOf, dif_pos i.isLt]

/-- The `n`th bit of a block is the `n`th bit of the symbol's index. -/
theorem getElem_code_eq (R : RankedAlphabet) (i : Fin R.card) (n : ℕ)
    (h : n < (R.code i).length) : (R.code i)[n] = i.val.testBit n := by
  simp only [code, List.getElem_map, List.getElem_range]

/-- The `n`th bit of a block's value is the block's `n`th entry. -/
theorem testBit_decodeBits : ∀ (bs : List Bool) (n : ℕ) (_ : n < bs.length),
    (decodeBits bs).testBit n = bs[n] :=
  List.rec (fun n h ↦ absurd h (by simp))
    (fun b bs ih n h ↦ by
      cases n with
      | zero =>
        rw [decodeBits_cons, Nat.testBit_zero, List.getElem_cons_zero]
        cases b <;> simp
      | succ n =>
        rw [decodeBits_cons, Nat.testBit_add_one]
        have hd : (2 * decodeBits bs + (if b then 1 else 0)) / 2 = decodeBits bs := by
          cases b <;> (simp only [Bool.false_eq_true, ite_false, ite_true]; omega)
        rw [hd, ih n (by simpa using h)]
        simp)

/-- Every arity a block yields is at most the largest, `arOf` returning an
arity only in the image of `arity`. -/
theorem le_maxArity_of_arOf_eq_some (R : RankedAlphabet) {v r : ℕ}
    (h : R.arOf v = some r) : r ≤ R.maxArity := by
  rw [arOf] at h
  split at h
  · rename_i hlt
    rw [← Option.some.inj h]
    exact arity_le_maxArity R ⟨v, hlt⟩
  · exact absurd h (by nofun)

end

end RankedAlphabet
