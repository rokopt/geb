/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic

/-!
# Ranked alphabets and their term algebras

A ranked alphabet names finitely many symbols, each with an arity and each
spelled by a block of bits of one common width. Its term algebra is the W-type
of the finitary polynomial functor whose shape type is `Fin card` and whose
direction family sends a symbol to `Fin` of its arity, so that all recursion
over terms is carried by `WType.elim` and `WType.rec`.

The unlabelled binary trees are the terms of `RankedAlphabet.Binary`'s
alphabet, of one symbol of arity zero and one of arity two.

## Main definitions

* `RankedAlphabet` — the alphabet.
* `RankedAlphabet.Term` — the term algebra.
* `RankedAlphabet.Term.mk` — the constructor, at the alphabet's own arities.
* `RankedAlphabet.Term.size` — the number of nodes.
* `RankedAlphabet.maxArity` — the largest arity of a symbol.

## Main statements

* `RankedAlphabet.Term.induction` — induction in the `Term.mk` presentation.
* `RankedAlphabet.size_le_sum_ofFn` — a child's node count is at most the sum
  over the children.
* `RankedAlphabet.arity_le_maxArity` — every symbol's arity is at most the
  largest.

## Implementation notes

`width_pos` is required rather than decorative. It is what gives
`t.size ≤ (spell t).length`, the fuel `Data/Tree/Ranked/Preorder.lean`'s
descent consumes, through `t.size ≤ width * t.size`; at width zero every
block is empty, so a one-symbol alphabet spells its unique term by the empty
word while the validity scan rejects that word, and the encoding is no
longer a bijection onto the words it accepts.

`Term` is `@[expose]`: without it `WType.mk` applications against
`Fin (R.arity i)` do not elaborate across the module boundary.

`Term.mk` exists because `WType.mk` at a concrete alphabet presents a child
family at type `Fin (R.arity ⟨v, h⟩)`, which is not syntactically `Fin 0` at
a nullary symbol; naming the constructor lets a caller write the arity once.
It is applied as `Term.mk R i ch` rather than `R.Term.mk i ch`: generalized
field notation resolves `R.Term` first, and that is a `Type`, which carries
no `mk`.

## Tags

ranked alphabet, term algebra, W-type, polynomial functor, arity
-/

/-- A ranked alphabet: `card` symbols, each spelled by a block of `width`
bits and each carrying an arity. `card_le_two_pow_width` admits an alphabet
whose size is not a power of two, at the price of blocks that spell no
symbol. -/
@[ext] public structure RankedAlphabet where
  /-- The number of symbols. -/
  card : ℕ
  /-- The number of bits spelling one symbol. -/
  width : ℕ
  /-- Every symbol's block is non-empty. -/
  width_pos : 0 < width
  /-- Every symbol has a block of the common width. -/
  card_le_two_pow_width : card ≤ 2 ^ width
  /-- The arity of each symbol. -/
  arity : Fin card → ℕ

namespace RankedAlphabet

public section

/-- The term algebra of a ranked alphabet. -/
@[expose] def Term (R : RankedAlphabet) : Type :=
  WType fun i : Fin R.card ↦ Fin (R.arity i)

/-- The term with head symbol `i` and children `ch`. -/
@[expose] def Term.mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) : R.Term :=
  WType.mk i ch

/-- The number of nodes of a term. -/
@[expose] def Term.size {R : RankedAlphabet} : R.Term → ℕ :=
  WType.elim ℕ fun x ↦ (List.ofFn x.2).sum + 1

/-- Induction in the `Term.mk` presentation, so that a proof driven by it
need not mention the underlying shape and direction families. -/
theorem Term.induction {R : RankedAlphabet} {motive : R.Term → Prop}
    (hmk : ∀ i ch, (∀ d, motive (ch d)) → motive (Term.mk R i ch)) :
    ∀ t, motive t :=
  WType.rec (motive := motive) fun i ch ih ↦ hmk i ch ih

@[simp] theorem size_mk {R : RankedAlphabet} (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    (Term.mk R i ch).size = (List.ofFn fun d ↦ (ch d).size).sum + 1 := rfl

/-- A child's node count is at most the sum over the children. Proved from
`List.rec` and `omega` rather than through the ordered-algebra API, whose
route to the same bound passes through instances the axiom linter rejects
for this module. -/
theorem size_le_sum_ofFn {R : RankedAlphabet} {n : ℕ} (ch : Fin n → R.Term)
    (d : Fin n) : (ch d).size ≤ (List.ofFn fun e ↦ (ch e).size).sum := by
  have hsum : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.sum := fun l ↦
    List.rec (fun x hx ↦ absurd hx (by simp))
      (fun a t iht x hx ↦ by
        rcases List.mem_cons.mp hx with h | h
        · subst h
          rw [List.sum_cons]
          omega
        · have := iht x h
          rw [List.sum_cons]
          omega) l
  exact hsum _ _ (List.mem_ofFn.mpr ⟨d, rfl⟩)

/-- The largest arity of a symbol of the alphabet, and zero at an alphabet
with no symbols. -/
@[expose] def maxArity (R : RankedAlphabet) : ℕ :=
  (List.ofFn R.arity).foldr max 0

/-- Every symbol's arity is at most the largest. Proved from `List.rec` and the
two `Nat.le_max` lemmas rather than through the ordered-algebra API, which is
the discipline `size_le_sum_ofFn` records for the sum. -/
theorem arity_le_maxArity (R : RankedAlphabet) (i : Fin R.card) :
    R.arity i ≤ R.maxArity := by
  have hmem : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := fun l ↦
    List.rec (fun x hx ↦ absurd hx (by simp))
      (fun a t iht x hx ↦ by
        rcases List.mem_cons.mp hx with h | h
        · subst h
          exact Nat.le_max_left _ _
        · exact Nat.le_trans (iht x h) (Nat.le_max_right _ _)) l
  exact hmem _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

end

end RankedAlphabet
