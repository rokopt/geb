/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.CobhamFoldProto.Expr

/-!
# The recognizer as the fold's degenerate instance

The fold of `Geb/Prototypes/Computability/CobhamFoldProto/Expr.lean` at the
terminal algebra — the carrier `Unit`, whose encoding is empty, so `p = 0` —
meets the recognizer of `Geb/Mathlib/Computability/Cobham/RankedTree.lean` at
each layer: the state layout, the dispatch window, the readout window, the bits
a step drops and prepends, and the accepted language.

The two are not one expression. `boundMulRaw_ne_boundRaw` separates the two
bound children at multiplicity one, at every growth, so the raw trees differ;
and the rejecting words differ, `foldOutSem_unit_eq_ite` giving `[false]`
where
`Cobham.isRankedSem_eq_ite` gives the empty bitstring. What holds is that each
component coincides and the languages agree.

## Main definitions

* `Geb.CobhamFold.encUnit`, `Geb.CobhamFold.decUnit` — the empty encoding of the
  terminal carrier and its inverse.
* `Geb.CobhamFold.algUnit` — the terminal algebra.

## Main statements

* `Geb.CobhamFold.dispatchWidthF_zero` — the dispatch window at `p = 0` is
  `Cobham.dispatchWidth`.
* `Geb.CobhamFold.stackBits_unit` — the stack's layout at `p = 0` is the
  pending count in unary.
* `Geb.CobhamFold.stateWordF_unit` — the state layout at `p = 0` is
  `Cobham.stateWord` of the projected state.
* `Geb.CobhamFold.readoutWidth_zero` — the readout window at `p = 0` is the
  recognizer's verdict window.
* `Geb.CobhamFold.dropCountF_unit`, `Geb.CobhamFold.nextPrefixF_unit` — the bits
  a step drops and prepends at `p = 0` are `Cobham.dropCount` and
  `Cobham.nextPrefix` of the projected state.
* `Geb.CobhamFold.foldOut_unit` — the fold at the terminal algebra is present
  exactly on the valid words.
* `Geb.CobhamFold.foldOutSem_unit_eq_ite` — the expression at the terminal
  algebra decides `RankedAlphabet.Valid`, pinning its value on both branches.

## Implementation notes

`nextPrefixF` branches on `Geb.CobhamFold.symOf` where `Cobham.nextPrefix`
branches on `RankedAlphabet.arOf`, and the two agree through
`Geb.CobhamFold.arOf_eq_map_symOf` rather than by reduction, which is why
`dropCountF_unit` and `nextPrefixF_unit` are proved by a case analysis rather
than stated as `rfl`.

`Cobham.isRankedSem_eq_ite` gives the recognizer's rejecting value as the empty
bitstring, while `foldOutSem_unit_eq_ite` gives `[false]`: `outWord` spells both
branches at the width `p + 1`, so that the marker alone separates them. The
languages the two accept are the same.

`one_le_one_mul_width` takes the multiplier one: the state carries one bit per pending
subterm and the count rises once per `R.width` input bits, so at `p = 0` the
state never exceeds the input by more than the flag and the slot, which is the
additive bound `Cobham.scan` already admits.

## References

* [Cobham1965]

## Tags

Cobham, ranked alphabet, fold, terminal algebra, recognizer
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

/-- The empty encoding of the terminal carrier. -/
@[nolint unusedArguments] def encUnit : Unit → Fin 0 → Bool := fun _ ↦ Fin.elim0

/-- The inverse of the empty encoding. -/
@[nolint unusedArguments] def decUnit : (Fin 0 → Bool) → Unit := fun _ ↦ ()

/-- The empty encoding's retraction, which holds by `Unit`'s eta. -/
theorem decUnit_encUnit : ∀ a : Unit, decUnit (encUnit a) = a := fun _ ↦ rfl

/-- The terminal algebra of a ranked alphabet. -/
@[nolint unusedArguments] def algUnit (R : RankedAlphabet) :
    (i : Fin R.card) → (Fin (R.arity i) → Unit) → Unit := fun _ _ ↦ ()

/-- The multiplier one meets the bound at `p = 0`. -/
theorem one_le_one_mul_width (R : RankedAlphabet) : 0 + 1 ≤ 1 * R.width := by
  have := R.width_pos
  omega

/-- The dispatch window at `p = 0` is the recognizer's. -/
theorem dispatchWidthF_zero (R : RankedAlphabet) :
    dispatchWidthF R 0 = dispatchWidth R := by
  rw [dispatchWidthF, dispatchWidth]
  omega

/-- The readout window at `p = 0` is the recognizer's verdict window, which
`Cobham.acceptTest` reads at `R.width + 3` bits. -/
theorem readoutWidth_zero (R : RankedAlphabet) :
    readoutWidth R 0 = R.width + 3 := by
  rw [readoutWidth]
  omega

/-- An entry at `p = 0` is the single `true` the unary count spells. -/
theorem entryBits_unit (a : Unit) : entryBits encUnit a = [true] := rfl

/-- The stack's layout at `p = 0` is the pending count in unary. -/
theorem stackBits_unit : ∀ st : List Unit,
    stackBits encUnit st = List.replicate st.length true :=
  List.rec rfl fun a t ih ↦ by
    rw [stackBits_cons, entryBits_unit, ih, List.length_cons, List.replicate_succ,
      List.cons_append, List.nil_append]

/-- The state layout at `p = 0` is `Cobham.stateWord` of the projected state. -/
theorem stateWordF_unit (R : RankedAlphabet) (s : FoldScan Unit) :
    stateWordF R encUnit s = stateWord R (toScan s) := by
  rw [stateWordF, stackBits_unit, stateWord, toScan]

/-- At `p = 0` the bits a step drops are the recognizer's. -/
theorem dropCountF_unit (R : RankedAlphabet) (b : Bool) (s : FoldScan Unit) :
    dropCountF R 0 b s = dropCount R b (toScan s) := by
  obtain ⟨buf, stack, live⟩ := s
  rw [dropCountF, dropCount, toScan]
  dsimp only
  cases live
  · rfl
  · dsimp only
    rw [arOf_eq_map_symOf]
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, decide_eq_true hlen]
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none => rfl
      | some i =>
        rw [Option.map_some]
        dsimp only
        by_cases hle : R.arity i ≤ stack.length
        · rw [if_pos hle, decide_eq_true hle, Nat.one_mul]
        · rw [if_neg hle, decide_eq_false hle]
    · rw [if_neg hlen, decide_eq_false hlen]

/-- At `p = 0` the bits a step prepends are the recognizer's: an entry is the
single `true` the pending count pushes. -/
theorem nextPrefixF_unit (R : RankedAlphabet) (b : Bool) (s : FoldScan Unit) :
    nextPrefixF R encUnit (algUnit R) b s = nextPrefix R b (toScan s) := by
  obtain ⟨buf, stack, live⟩ := s
  rw [nextPrefixF, nextPrefix, toScan]
  dsimp only
  cases live
  · rfl
  · dsimp only
    rw [arOf_eq_map_symOf]
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, decide_eq_true hlen]
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none => rfl
      | some i =>
        rw [Option.map_some]
        dsimp only
        by_cases hle : R.arity i ≤ stack.length
        · rw [dif_pos hle, decide_eq_true hle]
          rfl
        · rw [dif_neg hle, decide_eq_false hle]
    · rw [if_neg hlen, decide_eq_false hlen]

/-- The fold at the terminal algebra is present exactly on the valid words:
the recognizer is the fold's degenerate instance. -/
theorem foldOut_unit (R : RankedAlphabet) (w : List Bool) :
    foldOut R (algUnit R) w = if R.Valid w then some () else none := by
  by_cases hv : R.Valid w
  · rw [if_pos hv]
    have hcond := (foldOut_cond R (algUnit R) w).trans hv
    have h1 : (foldScanFinal R (algUnit R) w).stack.length = 1 :=
      eq_of_beq ((Bool.and_eq_true _ _).mp hcond).2
    rw [foldOut, hcond]
    match hst : (foldScanFinal R (algUnit R) w).stack with
    | [] =>
      rw [hst] at h1
      exact absurd h1 (by simp)
    | _ :: _ => rfl
  · rw [if_neg hv, foldOut, foldOut_cond]
    exact if_neg hv

/-- The expression at the terminal algebra decides `RankedAlphabet.Valid`, its
value pinned on both branches. -/
theorem foldOutSem_unit_eq_ite (R : RankedAlphabet) (w : List Bool) :
    foldOutSem R 0 encUnit decUnit decUnit_encUnit (algUnit R) 1 (one_le_one_mul_width R)
        ![w] =
      if R.Valid w then [true] else [false] := by
  rw [foldOutSem_eq, foldOut_unit]
  by_cases hv : R.Valid w
  · rw [if_pos hv, if_pos hv]
    rfl
  · rw [if_neg hv, if_neg hv]
    rfl

end Geb.CobhamFold

end
