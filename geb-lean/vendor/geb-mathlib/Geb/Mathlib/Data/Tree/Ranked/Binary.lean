/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Tree.Ranked.Preorder
public import Mathlib.Data.Fin.VecNotation

/-!
# The two-symbol ranked alphabet

The alphabet of one nullary and one binary symbol, spelled by one bit each.
Its terms are the unlabelled binary trees, the initial algebra of
`F X = 1 + X × X`, and its preorder encoding is `RankedAlphabet.spell` at
this alphabet.

At width one every block is a single bit, so the validity scan carries no
incomplete block and its state reduces to a pending count and a liveness
verdict. This module names that counter form and gives it one bit at a time,
which is the shape a recognizer over the encoding is stated against.

## Main definitions

* `RankedAlphabet.Binary.binRanked` — the alphabet.
* `RankedAlphabet.Binary.leaf`, `RankedAlphabet.Binary.node` — the two forms
  of its terms.
* `RankedAlphabet.Binary.depth`, `RankedAlphabet.Binary.ok` — the validity
  scan's pending count and its liveness verdict, read off a whole word.

## Main statements

* `RankedAlphabet.Binary.buf_scanFinal_eq_nil` — at width one no incomplete
  block survives a step.
* `RankedAlphabet.Binary.depth_le_length` — the pending count never exceeds
  the word length, which is the bound `Cobham.length_combSem_le` asks for.
* `RankedAlphabet.Binary.valid_iff_ok_and_depth_eq_one` — validity is the two
  conditions on the counter form, the third holding of every word.
* `RankedAlphabet.Binary.ok_cons_false`,
  `RankedAlphabet.Binary.ok_cons_true`,
  `RankedAlphabet.Binary.depth_cons_false_of_ok`,
  `RankedAlphabet.Binary.depth_cons_true_of_ok_of_two_le_depth` — the counter
  form one bit at a time.

## Implementation notes

`leafSym` and `nodeSym` name the two indices rather than each use site
writing `⟨0, by decide⟩`: a symbol index whose bound proof is still an
unassigned metavariable blocks `arity` from reducing, so the child family's
domain is then neither `Fin 0` nor `Fin 2` and the family does not elaborate.
Against a symbol index that is a pattern variable, a child index's bound is
ascribed rather than proved where it stands: the goal `0 < binRanked.arity
⟨1, h⟩` carries the free variable `h`, which `decide` refuses, and presents
the arity as an atom, which `omega` cannot unfold. `show (0 : ℕ) < 2` replaces
it with the definitionally equal closed goal.

`spell_leaf` and `spell_node` have no consumer in this module: they are kept
as the alphabet's characteristic spelling equations, stating what the
preorder encoding is at this alphabet, and so belong to its public interface
rather than to internal machinery.

`depth` and `ok` are `@[expose]`, as the declarations they project are: a
consuming module's `rfl` and `decide` reduce through them only if they unfold
across the module boundary. `ok_cons_false` and `ok_cons_true` are `@[simp]`,
being unconditional rewrite rules on that form; the two depth `cons`-lemmas
are not, since neither `ok w = true` nor `2 ≤ depth w` is a side condition
`simp` discharges here, so as simp rules they would be inert.

`scanStep_of_not_live` holds at any width — a failed scan absorbs whatever
the block layout — and is stated here because here is where it is used.

`decide_length_eq_width` proceeds by `cases b` rather than `decide` alone:
`decide` refuses a goal carrying a free variable, so the case analysis is what
closes `b`, even though `[b].length` is `1` either way.

`code_leafSym` and `code_nodeSym` are proved by `decide` rather than by `rfl`.
`Nat.land`, which `Nat.testBit` runs through, is not exposed, so a block does
not reduce during elaboration, while the kernel evaluates it.

## Tags

binary tree, ranked alphabet, term algebra, preorder, scan
-/

namespace RankedAlphabet.Binary

public section

/-- The alphabet of one nullary and one binary symbol, one bit to a block. -/
@[expose] def binRanked : RankedAlphabet := ⟨2, 1, Nat.one_pos, by decide, ![0, 2]⟩

/-- The nullary symbol. -/
@[expose] def leafSym : Fin binRanked.card := ⟨0, by decide⟩

/-- The binary symbol. -/
@[expose] def nodeSym : Fin binRanked.card := ⟨1, by decide⟩

/-- The term with the nullary head symbol. -/
@[expose] def leaf : binRanked.Term :=
  Term.mk binRanked leafSym fun d ↦ absurd (show d.val < 0 from d.isLt) (by omega)

/-- The term with the binary head symbol and children `l` and `r`. -/
@[expose] def node (l r : binRanked.Term) : binRanked.Term :=
  Term.mk binRanked nodeSym fun d ↦ if d.val = 0 then l else r

/-- The nullary symbol's block is the single `false` bit. -/
theorem code_leafSym : binRanked.code leafSym = [false] := by decide

/-- The binary symbol's block is the single `true` bit. -/
theorem code_nodeSym : binRanked.code nodeSym = [true] := by decide

/-- The nullary term is spelled by the single `false` bit. -/
@[simp] theorem spell_leaf : binRanked.spell leaf = [false] := by
  rw [leaf, spell_mk, code_leafSym]
  rfl

/-- A binary term is spelled by a `true` bit and its children's spellings. -/
@[simp] theorem spell_node (l r : binRanked.Term) :
    binRanked.spell (node l r) = true :: (binRanked.spell l ++ binRanked.spell r) := by
  rw [node, spell_mk, code_nodeSym]
  change [true] ++ (binRanked.spell l ++ (binRanked.spell r ++ [])) = _
  rw [List.append_nil]
  rfl

/-- The count of pending subterms the validity scan leaves. -/
@[expose] def depth (w : List Bool) : ℕ := (binRanked.scanFinal w).depth

/-- Whether the validity scan has not failed. -/
@[expose] def ok (w : List Bool) : Bool := (binRanked.scanFinal w).live

/-- At width one every block completes as it is read, so no incomplete block
survives a step. -/
theorem buf_scanFinal_eq_nil (w : List Bool) : (binRanked.scanFinal w).buf = [] := by
  have h : (binRanked.scanFinal w).buf.length < 1 := binRanked.length_buf_scanFinal_lt w
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- The pending count never exceeds the word length. -/
theorem depth_le_length (w : List Bool) : depth w ≤ w.length :=
  binRanked.depth_scanFinal_le_length w

/-- Validity is the counter form's two conditions: at width one the third,
that no incomplete block remains, holds of every word. -/
theorem valid_iff_ok_and_depth_eq_one (w : List Bool) :
    binRanked.Valid w ↔ ok w = true ∧ depth w = 1 := by
  rw [valid_iff_scanFinal]
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, buf_scanFinal_eq_nil w, h.2⟩⟩

/-- The block a bit completes has the alphabet's width. -/
theorem decide_length_eq_width (b : Bool) :
    decide (([b] : List Bool).length = binRanked.width) = true := by cases b <;> decide

/-- The nullary symbol's block denotes arity zero. -/
theorem arOf_decodeBits_false : binRanked.arOf (decodeBits [false]) = some 0 := by decide

/-- The binary symbol's block denotes arity two. -/
theorem arOf_decodeBits_true : binRanked.arOf (decodeBits [true]) = some 2 := by decide

/-- A leaf bit read by a live scan carrying no incomplete block: its arity is
zero, which every pending count admits. -/
theorem scanStep_false_of_live_of_buf_nil (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) : binRanked.scanStep false s = ⟨[], s.depth + 1, true⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_false]
  rfl

/-- A node bit read with two subterms pending pops both and pushes one. -/
theorem scanStep_true_of_live_of_buf_nil_of_two_le_depth (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) (h2 : 2 ≤ s.depth) :
    binRanked.scanStep true s = ⟨[], s.depth - 2 + 1, true⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_true]
  simp only []
  rw [decide_eq_true h2]

/-- A node bit read with fewer than two subterms pending fails the scan. -/
theorem scanStep_true_of_live_of_buf_nil_of_depth_lt_two (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) (h2 : s.depth < 2) :
    binRanked.scanStep true s = ⟨[], s.depth, false⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_true]
  simp only []
  rw [decide_eq_false (by omega : ¬ 2 ≤ s.depth)]

/-- A failed scan reads no further. -/
theorem scanStep_of_not_live (b : Bool) (s : Scan) (hl : s.live = false) :
    binRanked.scanStep b s = s := by
  rw [scanStep, hl]

/-- A leaf bit cannot fail. -/
@[simp] theorem ok_cons_false (w : List Bool) : ok (false :: w) = ok w := by
  rw [ok, ok, scanFinal_cons]
  cases h : (binRanked.scanFinal w).live
  · rw [scanStep_of_not_live false _ h, h]
  · rw [scanStep_false_of_live_of_buf_nil _ h (buf_scanFinal_eq_nil w)]

/-- A node bit fails when the scan has already failed, or when fewer than two
subterms are pending. -/
@[simp] theorem ok_cons_true (w : List Bool) :
    ok (true :: w) = (ok w && decide (2 ≤ depth w)) := by
  rw [ok, ok, depth, scanFinal_cons]
  cases h : (binRanked.scanFinal w).live
  · rw [scanStep_of_not_live true _ h, h, Bool.false_and]
  · rcases Nat.lt_or_ge (binRanked.scanFinal w).depth 2 with h2 | h2
    · rw [scanStep_true_of_live_of_buf_nil_of_depth_lt_two _ h (buf_scanFinal_eq_nil w) h2]
      dsimp only
      rw [decide_eq_false (by omega : ¬ 2 ≤ (binRanked.scanFinal w).depth), Bool.true_and]
    · rw [scanStep_true_of_live_of_buf_nil_of_two_le_depth _ h (buf_scanFinal_eq_nil w) h2]
      dsimp only
      rw [decide_eq_true h2, Bool.true_and]

/-- A leaf bit raises the pending count by one, the scan being live before
it. -/
theorem depth_cons_false_of_ok (w : List Bool) (h : ok w = true) :
    depth (false :: w) = depth w + 1 := by
  rw [depth, depth, scanFinal_cons,
    scanStep_false_of_live_of_buf_nil _ h (buf_scanFinal_eq_nil w)]

/-- A node bit pops two pending subterms and pushes one, the scan being live
before it and two subterms pending. -/
theorem depth_cons_true_of_ok_of_two_le_depth (w : List Bool) (h : ok w = true)
    (h2 : 2 ≤ depth w) : depth (true :: w) = depth w - 1 := by
  simp only [depth] at h2 ⊢
  rw [scanFinal_cons,
    scanStep_true_of_live_of_buf_nil_of_two_le_depth _ h (buf_scanFinal_eq_nil w) h2]
  dsimp only
  omega

end

end RankedAlphabet.Binary
