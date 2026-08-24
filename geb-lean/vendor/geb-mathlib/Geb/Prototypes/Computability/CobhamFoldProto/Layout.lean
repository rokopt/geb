/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.CobhamFoldProto.Fold
public import Geb.Mathlib.Computability.Cobham.RankedTree

/-!
# The fold scan's state as a bitstring

`Cobham.stateWord` lays `RankedAlphabet.Scan` out as a bitstring: the liveness
flag, the incomplete block in a slot of the alphabet's width, then the pending
count in unary. This module lays `Geb.CobhamFold.FoldScan` out the same way,
with the unary count replaced by one block per stack entry.

Each entry occupies `p + 1` bits: a `true` presence marker followed by the `p`
bits of the carrier's encoding. The marker is what the unary count's `true`
already was, so at `p = 0` — the carrier `Unit`, whose encoding is empty — the
layout is `Cobham.stateWord` and the dispatch window is
`Cobham.dispatchWidth`, which `Geb.CobhamFold.stateWordF_unit` and
`Geb.CobhamFold.dispatchWidthF_zero` state. The layout generalizes the
recognizer's rather than sitting beside it.

The marker is not redundant at `p > 0`. `Cobham.bits` pads a window past the
word's end with `false`, and a carrier value may encode to all-`false`, so
without a marker the padding would be indistinguishable from a stack entry. The
marker separates them: the run of markers gives the stack's height capped at the
window, which is what decides whether a symbol's arity is available.

## Main definitions

* `Geb.CobhamFold.entryBits`, `Geb.CobhamFold.stackBits` — one stack entry, and
  the stack, as bitstrings.
* `Geb.CobhamFold.stateWordF` — the fold scan's state as a bitstring.
* `Geb.CobhamFold.dispatchWidthF` — the number of state bits a step dispatches
  on.
* `Geb.CobhamFold.decodeStack`, `Geb.CobhamFold.decodeStateAt`,
  `Geb.CobhamFold.decodeStateF` — the inverse of the layout, at an arbitrary
  window and at the dispatch window.
* `Geb.CobhamFold.dropCountF`, `Geb.CobhamFold.nextPrefixF` — the bits a step
  drops and prepends.

## Main statements

* `Geb.CobhamFold.length_stackBits`, `Geb.CobhamFold.length_stateWordF_of_lt` —
  the layout's lengths.
* `Geb.CobhamFold.take_stackBits`, `Geb.CobhamFold.drop_stackBits`,
  `Geb.CobhamFold.drop_stackBits_mul` — the stack's layout truncated, advanced
  by one entry, and advanced by several.
* `Geb.CobhamFold.ofFn_bits_stateWordF` — the state word truncated to a window
  and zero-padded.
* `Geb.CobhamFold.decodeStateAt_stateWordF_of_lt`,
  `Geb.CobhamFold.decodeStateF_stateWordF_of_lt` — the decoder inverts the
  layout up to truncating the stack at the window.
* `Geb.CobhamFold.dropCountF_take_stack`, `Geb.CobhamFold.nextPrefixF_take_stack`
  — truncating the stack at the window changes neither.
* `Geb.CobhamFold.stateWordF_foldScanStep_of_lt` — a step rewrites a bounded
  prefix and drops a bounded number of bits.
* `Geb.CobhamFold.length_stateWordF_not_le_add` — at the two-symbol alphabet,
  whose width is one, the additive bound `Cobham.scan` admits fails of this
  layout at every positive carrier width.

## Implementation notes

`dispatchWidthF` reads `R.maxArity + 1` entries. `R.maxArity` of them are what a
symbol's algebra can consume; the extra one distinguishes a stack of exactly
`R.maxArity` entries from a longer one, which is what decides `r ≤ height` for
every arity `r`, `RankedAlphabet.le_maxArity_of_arOf_eq_some` bounding the
arities. This is `Cobham.dispatchWidth`'s `R.maxArity + 1` window, one entry
wide rather than one bit wide.

`decodeStack` recurses on a fuel argument by `Nat.rec` rather than on the word,
so no `def` here calls itself.

`decodeStateF` reads the stack through `List` operations rather than by `Fin`
arithmetic, for the reason `Cobham.decodeState` records: a branch family's
domain is `Fin (dispatchWidthF R p) → Bool` at a symbolic width, and indexing it
would carry a bound proof at every step, while `DecidableEq (Fin n → Bool)`
depends on `Classical.choice`: it resolves through
`FinEnum.decidablePiFinEnum`, which is choice-free, at mathlib's `FinEnum.fin`,
which is not.

The retraction hypothesis `∀ a, dec (enc a) = a` enters only at
`decodeStateF_stateWordF_of_lt`; the lengths and the step lemma hold whatever
`dec` does off the image of `enc`, as they do in
`Geb/Mathlib/Computability/Cobham/Fold.lean`.

## References

* [Cobham1965]

## Tags

Cobham, ranked alphabet, preorder, fold, state layout, stack
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

universe u

variable {α : Type u} {p : ℕ}

/-- One stack entry as a bitstring: a `true` presence marker followed by the
carrier's encoding. -/
def entryBits (enc : α → Fin p → Bool) (a : α) : List Bool :=
  true :: List.ofFn (enc a)

/-- The stack as a bitstring: one marked block per entry, the top entry
first. At `p = 0` this is the run of `true` `Cobham.stateWord` spells the
pending count with. -/
def stackBits (enc : α → Fin p → Bool) (st : List α) : List Bool :=
  st.flatMap (entryBits enc)

/-- The fold scan's state as a bitstring: the liveness flag, the block slot,
then the stack. -/
def stateWordF (R : RankedAlphabet) (enc : α → Fin p → Bool) (s : FoldScan α) :
    List Bool :=
  s.live :: bufBits R s.buf ++ stackBits enc s.stack

/-- The number of state bits a step dispatches on: the flag, the slot, and
`R.maxArity + 1` stack entries. -/
def dispatchWidthF (R : RankedAlphabet) (p : ℕ) : ℕ :=
  1 + R.width + (p + 1) * (R.maxArity + 1)

/-- An entry occupies the encoding's width plus its marker. -/
@[simp] theorem length_entryBits (enc : α → Fin p → Bool) (a : α) :
    (entryBits enc a).length = p + 1 := by
  rw [entryBits, List.length_cons, List.length_ofFn]

/-- The stack's layout is one entry's width per entry. -/
theorem length_stackBits (enc : α → Fin p → Bool) :
    ∀ st : List α, (stackBits enc st).length = (p + 1) * st.length :=
  List.rec rfl fun a t ih ↦ by
    rw [stackBits, List.flatMap_cons, List.length_append,
      length_entryBits, ← stackBits, ih, List.length_cons, Nat.mul_succ]
    omega

/-- The empty stack's layout. -/
@[simp] theorem stackBits_nil (enc : α → Fin p → Bool) :
    stackBits enc ([] : List α) = [] := rfl

/-- The stack's layout, one entry at a time. -/
@[simp] theorem stackBits_cons (enc : α → Fin p → Bool) (a : α) (st : List α) :
    stackBits enc (a :: st) = entryBits enc a ++ stackBits enc st := rfl

/-- The state word's length: the flag, the slot, and the stack. -/
theorem length_stateWordF_of_lt (R : RankedAlphabet) (enc : α → Fin p → Bool)
    (s : FoldScan α) (h : s.buf.length < R.width) :
    (stateWordF R enc s).length = 1 + R.width + (p + 1) * s.stack.length := by
  rw [stateWordF, List.cons_append, List.length_cons, List.length_append,
    length_bufBits_of_lt R s.buf h, length_stackBits]
  omega

/-- The stack's layout truncated to a whole number of entries is the layout of
the truncated stack. -/
theorem take_stackBits (enc : α → Fin p → Bool) :
    ∀ (st : List α) (m : ℕ),
      (stackBits enc st).take ((p + 1) * m) = stackBits enc (st.take m) :=
  List.rec (fun _ ↦ by rw [stackBits_nil, List.take_nil, List.take_nil, stackBits_nil])
    (fun a t ih m ↦ match m with
      | 0 => by rw [Nat.mul_zero, List.take_zero, List.take_zero, stackBits_nil]
      | k + 1 => by
        have hlen : (p + 1) * (k + 1) = (entryBits enc a).length + (p + 1) * k := by
          rw [length_entryBits, Nat.mul_succ]
          omega
        rw [stackBits_cons, hlen, List.take_length_add_append, ih k,
          List.take_succ_cons, stackBits_cons])

/-- The stack's layout advanced past its first entry is the layout of the
rest. -/
theorem drop_stackBits (enc : α → Fin p → Bool) (a : α) (st : List α) :
    (stackBits enc (a :: st)).drop (p + 1) = stackBits enc st := by
  rw [stackBits_cons]
  exact List.drop_left' (length_entryBits enc a)

/-- The stack's layout advanced past a whole number of entries is the layout of
the stack advanced by that many. -/
theorem drop_stackBits_mul (enc : α → Fin p → Bool) :
    ∀ (n : ℕ) (st : List α),
      (stackBits enc st).drop ((p + 1) * n) = stackBits enc (st.drop n) :=
  Nat.rec (fun st ↦ by rw [Nat.mul_zero, List.drop_zero, List.drop_zero])
    (fun k ih st ↦ match st with
      | [] => by rw [stackBits_nil, List.drop_nil, List.drop_nil, stackBits_nil]
      | a :: t => by
        have hmul : (p + 1) * (k + 1) = (p + 1) + (p + 1) * k := by
          rw [Nat.mul_succ]
          omega
        rw [hmul, ← List.drop_drop, drop_stackBits, ih t, List.drop_succ_cons])

/-- The bits of a spelled-out family followed by anything are that family: the
window reads only the family's own width. -/
theorem bits_ofFn_append (f : Fin p → Bool) (l : List Bool) :
    bits p (List.ofFn f ++ l) = f := by
  funext j
  have hj : j.val < (List.ofFn f).length := by
    rw [List.length_ofFn]
    exact j.isLt
  rw [bits, List.getD_eq_getElem?_getD, List.getElem?_append_left hj,
    List.getElem?_eq_getElem hj, List.getElem_ofFn]
  rfl

/-- The state word truncated to a window of whole entries past the slot, and
zero-padded: the flag, the slot, the stack truncated at the window, and padding
where the stack is shorter. Stated at an arbitrary window, the dispatch and the
verdict reading different ones. -/
theorem ofFn_bits_stateWordF (R : RankedAlphabet) (enc : α → Fin p → Bool)
    (s : FoldScan α) (n m : ℕ) (hn : n = 1 + R.width + (p + 1) * m)
    (h : s.buf.length < R.width) :
    List.ofFn (bits n (stateWordF R enc s)) =
      s.live :: (bufBits R s.buf ++
        (stackBits enc (s.stack.take m) ++
          List.replicate ((p + 1) * m - (p + 1) * s.stack.length) false)) := by
  subst hn
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hdw : 1 + R.width + (p + 1) * m = (bufBits R s.buf).length + ((p + 1) * m) + 1 := by
    rw [hbuf]
    omega
  have hpad : 1 + R.width + (p + 1) * m - (stateWordF R enc s).length =
      (p + 1) * m - (p + 1) * s.stack.length := by
    rw [length_stateWordF_of_lt R enc s h]
    omega
  rw [ofFn_bits, hpad, stateWordF, List.cons_append, hdw, List.take_succ_cons,
    List.take_length_add_append, take_stackBits, List.cons_append,
    List.append_assoc]

/-- The validity scan of a word of leaves has one pending subterm per leaf.
At the two-symbol alphabet a block is one bit and `false` spells the nullary
symbol, so nothing is ever popped. -/
private theorem scanFinal_replicate_false : ∀ k : ℕ,
    Binary.binRanked.scanFinal (List.replicate k false) = ⟨[], k, true⟩ :=
  Nat.rec (motive := fun k ↦
      Binary.binRanked.scanFinal (List.replicate k false) = ⟨[], k, true⟩) rfl
    fun k ih ↦ by
      beta_reduce
      rw [List.replicate_succ, scanFinal_cons, ih,
        Binary.scanStep_false_of_live_of_buf_nil _ rfl rfl]

/-- At the two-symbol alphabet, whose width is one, the additive bound
`Cobham.scan` admits fails of this layout at every positive carrier width, so
the multiplicative bound `Geb.CobhamFold.scanMul` carries is not a convenience.
A word of `k` leaves leaves `k` entries on the stack, giving a state of
`2 + (q + 1) * k` bits against an input of `k`; no fixed `growth` dominates
that. The failure needs `R.width < q + 1`, and needs an alphabet whose symbols
grow the stack: at `R.width ≥ q + 1` the additive bound always suffices, and an
alphabet with no nullary symbol keeps the stack empty whatever the carrier. -/
theorem length_stateWordF_not_le_add {β : Type u} {q : ℕ} (hq : 0 < q)
    (enc : β → Fin q → Bool)
    (alg : (i : Fin Binary.binRanked.card) →
      (Fin (Binary.binRanked.arity i) → β) → β) (growth : ℕ) :
    ∃ w : List Bool, w.length + growth <
      (stateWordF Binary.binRanked enc
        (foldScanFinal Binary.binRanked alg w)).length := by
  refine ⟨List.replicate growth false, ?_⟩
  have hproj :=
    toScan_foldScanFinal Binary.binRanked alg (List.replicate growth false)
  rw [scanFinal_replicate_false] at hproj
  have hbuf :
      (foldScanFinal Binary.binRanked alg (List.replicate growth false)).buf = [] :=
    congrArg Scan.buf hproj
  have hstack :
      (foldScanFinal Binary.binRanked alg
        (List.replicate growth false)).stack.length = growth :=
    congrArg Scan.depth hproj
  rw [length_stateWordF_of_lt Binary.binRanked enc _
      (by rw [hbuf]; exact Binary.binRanked.width_pos),
    hstack, List.length_replicate]
  have hw : Binary.binRanked.width = 1 := rfl
  rw [hw, Nat.add_mul, Nat.one_mul]
  have hle : 1 * growth ≤ q * growth := Nat.mul_le_mul_right growth hq
  rw [Nat.one_mul] at hle
  omega

/-- The inverse of the stack's layout, read off a bitstring with a fuel bound:
each marked block contributes its decoded value, and the first unmarked block
ends the stack. -/
def decodeStack (dec : (Fin p → Bool) → α) : ℕ → List Bool → List α :=
  Nat.rec (motive := fun _ ↦ List Bool → List α) (fun _ ↦ [])
    fun _ ih l ↦
      match l with
      | true :: rest => dec (bits p rest) :: ih (rest.drop p)
      | _ => []

/-- The decoder at no fuel reads no entry. -/
@[simp] theorem decodeStack_zero (dec : (Fin p → Bool) → α) (l : List Bool) :
    decodeStack dec 0 l = [] := rfl

/-- The decoder's computation rule at a marked block. -/
theorem decodeStack_succ_true (dec : (Fin p → Bool) → α) (k : ℕ)
    (rest : List Bool) :
    decodeStack dec (k + 1) (true :: rest) =
      dec (bits p rest) :: decodeStack dec k (rest.drop p) := rfl

/-- The decoder inverts the stack's layout, up to truncating at the fuel.
The retraction hypothesis is what identifies each decoded block with the value
that spelled it; the trailing `false` padding stops the recursion. -/
theorem decodeStack_stackBits_append (dec : (Fin p → Bool) → α)
    (enc : α → Fin p → Bool) (hdec : ∀ a, dec (enc a) = a) :
    ∀ (k : ℕ) (st : List α) (j : ℕ),
      decodeStack dec k (stackBits enc st ++ List.replicate j false) = st.take k :=
  Nat.rec (fun st _ ↦ by rw [decodeStack_zero, List.take_zero])
    (fun k ih st j ↦ match st with
      | [] => by
        match j with
        | 0 => rfl
        | _ + 1 => rfl
      | a :: t => by
        rw [stackBits_cons, entryBits]
        simp only [List.cons_append, List.append_assoc]
        rw [decodeStack_succ_true, bits_ofFn_append, hdec,
          List.drop_left' (List.length_ofFn (f := enc a)), ih t j,
          List.take_succ_cons])

/-- The inverse of the state layout at a window of `n` bits reading `m` stack
entries: the flag is the head, the block is the slot past its padding and
sentinel, and the stack is decoded from what follows the slot. Stated at an
arbitrary window, the dispatch and the readout reading different ones. -/
def decodeStateAt (R : RankedAlphabet) (p : ℕ) (dec : (Fin p → Bool) → α)
    (n m : ℕ) (v : Fin n → Bool) : FoldScan α :=
  ⟨(((List.ofFn v).tail.take R.width).dropWhile (fun b ↦ !b)).tail,
    decodeStack dec m ((List.ofFn v).tail.drop R.width),
    (List.ofFn v).headD false⟩

/-- The decoder inverts the layout, up to truncating the stack at the window. -/
theorem decodeStateAt_stateWordF_of_lt (R : RankedAlphabet)
    (dec : (Fin p → Bool) → α) (enc : α → Fin p → Bool)
    (hdec : ∀ a, dec (enc a) = a) (s : FoldScan α) (n m : ℕ)
    (hn : n = 1 + R.width + (p + 1) * m) (h : s.buf.length < R.width) :
    decodeStateAt R p dec n m (bits n (stateWordF R enc s)) =
      { s with stack := s.stack.take m } := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hword := ofFn_bits_stateWordF R enc s n m hn h
  have hslot : ((List.ofFn (bits n (stateWordF R enc s))).tail.take
      R.width) = bufBits R s.buf := by
    rw [hword, List.tail_cons, List.take_left' hbuf]
  have htail : ((List.ofFn (bits n (stateWordF R enc s))).tail.drop
      R.width) = stackBits enc (s.stack.take m) ++
        List.replicate ((p + 1) * m - (p + 1) * s.stack.length) false := by
    rw [hword, List.tail_cons, List.drop_left' hbuf]
  refine FoldScan.ext ?_ ?_ ?_
  · rw [decodeStateAt, hslot, dropWhile_bufBits]
    rfl
  · rw [decodeStateAt, htail, decodeStack_stackBits_append dec enc hdec,
      List.take_take, Nat.min_self]
  · rw [decodeStateAt, hword, List.headD_cons]

/-- The decoder at the dispatch window. -/
def decodeStateF (R : RankedAlphabet) (p : ℕ) (dec : (Fin p → Bool) → α)
    (v : Fin (dispatchWidthF R p) → Bool) : FoldScan α :=
  decodeStateAt R p dec (dispatchWidthF R p) (R.maxArity + 1) v

/-- The decoder inverts the layout, up to truncating the stack at the dispatch
window `R.maxArity + 1`. -/
theorem decodeStateF_stateWordF_of_lt (R : RankedAlphabet)
    (dec : (Fin p → Bool) → α) (enc : α → Fin p → Bool)
    (hdec : ∀ a, dec (enc a) = a) (s : FoldScan α)
    (h : s.buf.length < R.width) :
    decodeStateF R p dec (bits (dispatchWidthF R p) (stateWordF R enc s)) =
      { s with stack := s.stack.take (R.maxArity + 1) } :=
  decodeStateAt_stateWordF_of_lt R dec enc hdec s (dispatchWidthF R p)
    (R.maxArity + 1) (by rw [dispatchWidthF]) h

/-- The bits a step drops from the state word: the flag and the slot, together
with the entries the symbol of a completed block pops. -/
def dropCountF (R : RankedAlphabet) (p : ℕ) (b : Bool) (s : FoldScan α) : ℕ :=
  match s.live with
  | false => 1 + R.width
  | true =>
    if (b :: s.buf).length = R.width then
      match symOf R (decodeBits (b :: s.buf)) with
      | none => 1 + R.width
      | some i =>
        if R.arity i ≤ s.stack.length then 1 + R.width + (p + 1) * R.arity i
        else 1 + R.width
    else 1 + R.width

/-- The bits a step prepends to the state word: the rebuilt flag and slot,
together with the entry the symbol of a completed block pushes. -/
def nextPrefixF (R : RankedAlphabet) (enc : α → Fin p → Bool)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool)
    (s : FoldScan α) : List Bool :=
  match s.live with
  | false => false :: bufBits R s.buf
  | true =>
    if (b :: s.buf).length = R.width then
      match symOf R (decodeBits (b :: s.buf)) with
      | none => false :: bufBits R []
      | some i =>
        if h : R.arity i ≤ s.stack.length then
          true :: bufBits R [] ++
            entryBits enc (alg i fun d ↦ s.stack[d.val]'(Nat.lt_of_lt_of_le d.isLt h))
        else false :: bufBits R []
    else true :: bufBits R (b :: s.buf)

/-- Truncating the stack at the dispatch window leaves the bits dropped
unchanged: the only test reading the stack's height compares it with an arity,
which `RankedAlphabet.arity_le_maxArity` bounds by `R.maxArity`. -/
theorem dropCountF_take_stack (R : RankedAlphabet) (p : ℕ) (b : Bool)
    (s : FoldScan α) :
    dropCountF R p b { s with stack := s.stack.take (R.maxArity + 1) } =
      dropCountF R p b s := by
  obtain ⟨buf, stack, live⟩ := s
  rw [dropCountF, dropCountF]
  dsimp only
  cases live
  · rfl
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, if_pos hlen]
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none => rfl
      | some i =>
        dsimp only
        have hle : R.arity i ≤ R.maxArity := arity_le_maxArity R i
        have hmin : (stack.take (R.maxArity + 1)).length =
            min (R.maxArity + 1) stack.length := List.length_take
        by_cases hst : R.arity i ≤ stack.length
        · rw [if_pos hst, if_pos (by rw [hmin]; omega)]
        · rw [if_neg hst, if_neg (by rw [hmin]; omega)]
    · rw [if_neg hlen, if_neg hlen]

/-- Truncating the stack at the dispatch window leaves the bits prepended
unchanged: the entries the algebra reads are the first `R.arity i`, and the
window holds `R.maxArity + 1` of them. -/
theorem nextPrefixF_take_stack (R : RankedAlphabet) (enc : α → Fin p → Bool)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool)
    (s : FoldScan α) :
    nextPrefixF R enc alg b { s with stack := s.stack.take (R.maxArity + 1) } =
      nextPrefixF R enc alg b s := by
  obtain ⟨buf, stack, live⟩ := s
  rw [nextPrefixF, nextPrefixF]
  dsimp only
  cases live
  · rfl
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, if_pos hlen]
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none => rfl
      | some i =>
        dsimp only
        have hle : R.arity i ≤ R.maxArity := arity_le_maxArity R i
        have hmin : (stack.take (R.maxArity + 1)).length =
            min (R.maxArity + 1) stack.length := List.length_take
        by_cases hst : R.arity i ≤ stack.length
        · rw [dif_pos hst, dif_pos (by rw [hmin]; omega)]
          refine congrArg₂ List.cons rfl (congrArg₂ List.append rfl
            (congrArg (entryBits enc) (congrArg (alg i) (funext fun d ↦ ?_))))
          exact List.getElem_take
        · rw [dif_neg hst, dif_neg (by rw [hmin]; omega)]
    · rw [if_neg hlen, if_neg hlen]

/-- A step of the fold scan rewrites a bounded prefix of the state word and
drops a bounded number of its bits: the flag and the slot are rebuilt, and the
stack in the tail is popped by the arity of a completed block's symbol and
pushed with the algebra's value. -/
theorem stateWordF_foldScanStep_of_lt (R : RankedAlphabet)
    (enc : α → Fin p → Bool)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool)
    (s : FoldScan α) (h : s.buf.length < R.width) :
    stateWordF R enc (foldScanStep R alg b s) =
      nextPrefixF R enc alg b s ++
        (stateWordF R enc s).drop (dropCountF R p b s) := by
  have hpre : (s.live :: bufBits R s.buf).length = 1 + R.width := by
    rw [List.length_cons, length_bufBits_of_lt R s.buf h]
    omega
  have hdrop : (stateWordF R enc s).drop (1 + R.width) = stackBits enc s.stack :=
    List.drop_left' hpre
  have hdropr : ∀ n : ℕ, (stateWordF R enc s).drop (1 + R.width + (p + 1) * n) =
      stackBits enc (s.stack.drop n) := fun n ↦ by
    rw [← List.drop_drop, hdrop, drop_stackBits_mul]
  obtain ⟨buf, stack, live⟩ := s
  dsimp only at hdrop hdropr
  rw [foldScanStep, dropCountF, nextPrefixF]
  dsimp only
  cases live
  · dsimp only
    rw [hdrop]
    rfl
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, if_pos hlen, if_pos hlen]
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none =>
        dsimp only
        rw [hdrop]
        rfl
      | some i =>
        dsimp only
        by_cases hst : R.arity i ≤ stack.length
        · rw [dif_pos hst, if_pos hst, dif_pos hst, hdropr (R.arity i),
            stateWordF, List.cons_append, List.append_assoc]
          rfl
        · rw [dif_neg hst, if_neg hst, dif_neg hst, hdrop]
          rfl
    · rw [if_neg hlen, if_neg hlen, if_neg hlen, hdrop]
      rfl

end Geb.CobhamFold

end
