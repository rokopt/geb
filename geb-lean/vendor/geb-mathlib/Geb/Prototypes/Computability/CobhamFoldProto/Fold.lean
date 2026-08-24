/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.Tree.Ranked.Preorder
import Geb.Mathlib.Data.W.Basic

/-!
# The fold scan of a preorder spelling

`RankedAlphabet.scanStep` reads a preorder spelling right to left, carrying an
incomplete block, a count of pending subterms and a liveness flag. At a
completed block the symbol pops its arity from the count and pushes one, so the
count is the height of a stack whose entries carry no data.

This module replaces that count by a stack of values of an arbitrary carrier
and the pop-push by an application of an algebra of the ranked alphabet.
`toScan` projects the resulting state onto `RankedAlphabet.Scan` by taking the
stack's length, and `toScan_foldScanStep` shows the projection is a step
homomorphism at every carrier and every algebra: the validity scan is the
image of the fold scan under the terminal map, not a separate construction.

`foldOut` reads the final state as an `Option`, absent exactly where the word
spells no term, and `foldOut_eq` identifies it with `RankedAlphabet.parse`
followed by the fold. `R.Term` is the initial algebra of the alphabet, so that
fold is the unique algebra morphism out of it.

## Main definitions

* `Geb.CobhamFold.symOf` — the symbol a block denotes, refining
  `RankedAlphabet.arOf`, which returns only its arity.
* `Geb.CobhamFold.Term.fold` — the unique algebra morphism out of the term
  algebra.
* `Geb.CobhamFold.FoldScan` — the fold scan's state.
* `Geb.CobhamFold.foldScanStep`, `Geb.CobhamFold.foldScanFrom`,
  `Geb.CobhamFold.foldScanFinal` — one step, the scan from a state, and the
  scan from the initial state.
* `Geb.CobhamFold.toScan` — the projection onto `RankedAlphabet.Scan`.
* `Geb.CobhamFold.foldOut` — the final state read as an `Option`.

## Main statements

* `Geb.CobhamFold.arOf_eq_map_symOf` — `RankedAlphabet.arOf` is `symOf`
  followed by the arity.
* `Geb.CobhamFold.toScan_foldScanStep`, `Geb.CobhamFold.toScan_foldScanFinal` —
  the projection is a step homomorphism, and carries the whole scan.
* `Geb.CobhamFold.mem_stack_foldScanFinal` — every value on the scan's stack
  is one the algebra produced.
* `Geb.CobhamFold.foldScanFrom_code` — a completed block pops its arity's worth
  of stack and pushes the algebra applied to them.
* `Geb.CobhamFold.foldScanFrom_ofFn` — a family of spellings pushes one value
  each, in index order.
* `Geb.CobhamFold.foldScanFrom_spell` — a spelling pushes one value, the fold
  of the term it spells.
* `Geb.CobhamFold.Term.fold_unique` — the term algebra is initial, so `Term.fold`
  is the algebra morphism out of it rather than one of several.
* `Geb.CobhamFold.Term.fold_map`, `Geb.CobhamFold.foldOut_map` — fold fusion,
  and the agreement of two folds at different carriers whose algebras commute
  with a map.
* `Geb.CobhamFold.foldOut_eq` — the fold scan computes `RankedAlphabet.parse`
  followed by `Term.fold`.
* `Geb.CobhamFold.buf_foldScanFinal`,
  `Geb.CobhamFold.length_stack_foldScanFinal`,
  `Geb.CobhamFold.length_buf_foldScanFinal_lt` — the projection's consequences
  for the incomplete block and the stack's height, which every state layout over
  this scan consumes.
* `Geb.CobhamFold.width_mul_depth_add_length_buf_scanFinal_le` — the sharper
  bound on the pending count: the alphabet's width times the count, plus the
  incomplete block, is at most the word's length.
* `Geb.CobhamFold.width_mul_depth_scanFinal_le` — its corollary dropping the
  incomplete block, `R.width * depth ≤ |w|`.

## Implementation notes

The stack's head is the value of the term spelled immediately to the right of
the symbol being read, which is that symbol's child zero: scanning right to
left, `RankedAlphabet.scanFrom_append` reads the later part of a word first, so
within a symbol's children the last one scanned — and so the one pushed last —
is child zero. `foldScanStep` therefore indexes the algebra's argument by
position in the stack directly.

`foldScanStep` branches by `dite` where `RankedAlphabet.scanStep` branches by a
`match` on `decide`: the arity branch needs the comparison's proof to index the
stack, which a `match` on a `Bool` does not supply.

`symOf` is what `RankedAlphabet.arOf` would be if the scan needed the symbol
rather than its arity; `arOf_eq_map_symOf` is what makes the two scans branch
alike, and so what `toScan_foldScanStep` rests on.

`width_mul_depth_add_length_buf_scanFinal_le` sharpens
`RankedAlphabet.depth_scanFinal_le_length` by the alphabet's width. The pending
count rises only at a completed block, so it counts symbols rather than bits.
The invariant carries the incomplete block's length because a partial block is
progress toward the next increment; without that summand the induction does not
close at the completing step. `omega` treats the products as atoms, so the
completing step supplies the two linear facts relating them.

## References

* [GambinoHyland2004]

## Tags

ranked alphabet, preorder, scan, fold, catamorphism, initial algebra
-/

@[expose] public section

namespace Geb.CobhamFold

open RankedAlphabet

universe u v

variable {α : Type u} {β : Type v}

/-- The symbol a block denotes, absent at a block denoting none.
`RankedAlphabet.arOf` returns that symbol's arity; a fold needs the symbol
itself, to select the algebra's operation. -/
def symOf (R : RankedAlphabet) (v : ℕ) : Option (Fin R.card) :=
  if h : v < R.card then some ⟨v, h⟩ else none

/-- The arity of a block's symbol is the arity of what `symOf` returns, so the
validity scan and the fold scan take the same branch at every block. -/
theorem arOf_eq_map_symOf (R : RankedAlphabet) (v : ℕ) :
    R.arOf v = (symOf R v).map R.arity := by
  rw [arOf, symOf]
  split <;> rfl

/-- A block denotes the symbol it spells. -/
theorem symOf_decodeBits_code (R : RankedAlphabet) (i : Fin R.card) :
    symOf R (decodeBits (R.code i)) = some i := by
  rw [decodeBits_code, symOf, dif_pos i.isLt]

/-- The unique algebra morphism out of the term algebra: the fold of a term at
an algebra of the ranked alphabet. `RankedAlphabet.Term` is that alphabet's
W-type, so the morphism is its eliminator. -/
def Term.fold (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) : R.Term → α :=
  WType.elim α fun x ↦ alg x.1 x.2

/-- The fold on a term, in the `RankedAlphabet.Term.mk` presentation. -/
@[simp] theorem Term.fold_mk (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    Term.fold R alg (Term.mk R i ch) = alg i fun d ↦ Term.fold R alg (ch d) := rfl

/-- The term algebra is initial: a map commuting with the algebra is the fold,
so `Term.fold` is the algebra morphism out of it rather than one of several.
`RankedAlphabet.Term` is a `WType`, so this is `WType.elim_unique` at the
alphabet's shape and direction families, read at a point; the initiality it
expresses is [GambinoHyland2004]'s for polynomial functors. -/
theorem Term.fold_unique (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (f : R.Term → α)
    (hf : ∀ (i : Fin R.card) (ch : Fin (R.arity i) → R.Term),
      f (Term.mk R i ch) = alg i fun d ↦ f (ch d)) :
    ∀ t : R.Term, f t = Term.fold R alg t :=
  congrFun (WType.elim_unique
    (fun x : Σ i : Fin R.card, Fin (R.arity i) → α ↦ alg x.1 x.2) f hf)

/-- Fold fusion: a map commuting with two algebras carries one fold to the
other. A corollary of initiality, and the statement that identifies the results
of two fold constructions at different carriers. -/
theorem Term.fold_map (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α)
    (algV : (i : Fin R.card) → (Fin (R.arity i) → β) → β) (e : α → β)
    (he : ∀ (i : Fin R.card) (g : Fin (R.arity i) → α),
      algV i (fun d ↦ e (g d)) = e (alg i g)) :
    ∀ t : R.Term, Term.fold R algV t = e (Term.fold R alg t) :=
  fun t ↦ (Term.fold_unique R algV (fun t ↦ e (Term.fold R alg t))
    (fun i ch ↦ by
      beta_reduce
      rw [Term.fold_mk]
      exact (he i fun d ↦ Term.fold R alg (ch d)).symm) t).symm

/-- The state of the fold scan: the bits of an incomplete block, the stack of
values of the subterms already scanned, and whether the scan has failed.
`RankedAlphabet.Scan` is this state with the stack replaced by its length. -/
@[ext] structure FoldScan (α : Type u) where
  /-- The bits of an incomplete block, most recently read first. -/
  buf : List Bool
  /-- The values of the subterms already scanned, the most recently completed
  first. -/
  stack : List α
  /-- Whether the scan has not yet failed. -/
  live : Bool

/-- The projection onto the validity scan's state: the stack's length is the
pending count. -/
def toScan (s : FoldScan α) : Scan := ⟨s.buf, s.stack.length, s.live⟩

/-- One step of the fold scan, reading one bit. A failed state absorbs. An
incomplete block takes the bit; a complete one is decoded, and its symbol pops
its arity's worth of stack, applies the algebra to them and pushes the result,
failing when the block spells no symbol or the stack is short of the arity. -/
def foldScanStep (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool)
    (s : FoldScan α) : FoldScan α :=
  match s.live with
  | false => s
  | true =>
    if (b :: s.buf).length = R.width then
      match symOf R (decodeBits (b :: s.buf)) with
      | none => ⟨[], s.stack, false⟩
      | some i =>
        if h : R.arity i ≤ s.stack.length then
          ⟨[], alg i (fun d ↦ s.stack[d.val]'(Nat.lt_of_lt_of_le d.isLt h)) ::
            s.stack.drop (R.arity i), true⟩
        else ⟨[], s.stack, false⟩
    else ⟨b :: s.buf, s.stack, true⟩

/-- The projection is a step homomorphism: the validity scan is the fold scan
at every carrier and every algebra, read through the stack's length. -/
theorem toScan_foldScanStep (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool)
    (s : FoldScan α) :
    toScan (foldScanStep R alg b s) = R.scanStep b (toScan s) := by
  obtain ⟨buf, stack, live⟩ := s
  change toScan (foldScanStep R alg b ⟨buf, stack, live⟩) =
    R.scanStep b ⟨buf, stack.length, live⟩
  rw [foldScanStep, scanStep]
  dsimp only
  cases live
  · rfl
  · dsimp only
    rw [arOf_eq_map_symOf]
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, decide_eq_true hlen]
      dsimp only
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none => rfl
      | some i =>
        rw [Option.map_some]
        dsimp only
        by_cases hle : R.arity i ≤ stack.length
        · rw [dif_pos hle, decide_eq_true hle]
          exact Scan.ext rfl (by rw [toScan, List.length_cons, List.length_drop]) rfl
        · rw [dif_neg hle, decide_eq_false hle]
          rfl
    · rw [if_neg hlen, decide_eq_false hlen]
      rfl

/-- The fold scan of a word from a given state. `foldr` reads the word's last
bit first, which is the processing order of a right-to-left scan. -/
def foldScanFrom (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool)
    (s : FoldScan α) : FoldScan α :=
  w.foldr (foldScanStep R alg) s

/-- The fold scan of a word from the initial state. -/
def foldScanFinal (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    FoldScan α :=
  foldScanFrom R alg w ⟨[], [], true⟩

/-- The fold scan of the empty word. -/
@[simp] theorem foldScanFrom_nil (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (s : FoldScan α) :
    foldScanFrom R alg [] s = s := rfl

/-- The fold scan of a word, one bit at a time. -/
@[simp] theorem foldScanFrom_cons (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool)
    (w : List Bool) (s : FoldScan α) :
    foldScanFrom R alg (b :: w) s = foldScanStep R alg b (foldScanFrom R alg w s) :=
  rfl

/-- Every value on the fold scan's stack is one the algebra produced: the
stack starts empty, and the completing pop is the only clause that pushes. -/
theorem mem_stack_foldScanFinal (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (P : α → Prop)
    (hpush : ∀ (i : Fin R.card) (f : Fin (R.arity i) → α), P (alg i f)) :
    ∀ (w : List Bool), ∀ v ∈ (foldScanFinal R alg w).stack, P v :=
  List.rec (fun v hv ↦ absurd hv (by simp [foldScanFinal, foldScanFrom]))
    fun b u ih v hv ↦ by
    have hcons : foldScanFinal R alg (b :: u) =
        foldScanStep R alg b (foldScanFinal R alg u) := rfl
    rw [hcons, foldScanStep] at hv
    -- `foldScanFinal R alg u` is a term, not a local variable, so `obtain` on
    -- it would introduce fresh locals and rewrite neither `hv` nor `ih`. The
    -- named equation is what carries the split into both.
    rcases hfs : foldScanFinal R alg u with ⟨buf, stack, live⟩
    rw [hfs] at hv ih
    dsimp only at hv ih ⊢
    cases live
    · exact ih v hv
    · dsimp only at hv
      by_cases hlen : (b :: buf).length = R.width
      · rw [if_pos hlen] at hv
        match hsym : symOf R (decodeBits (b :: buf)) with
        | none =>
          rw [hsym] at hv
          exact ih v hv
        | some i =>
          rw [hsym] at hv
          dsimp only at hv
          by_cases hst : R.arity i ≤ stack.length
          · rw [dif_pos hst] at hv
            rcases List.mem_cons.mp hv with h | h
            · exact h ▸ hpush i _
            · exact ih v (List.mem_of_mem_drop h)
          · rw [dif_neg hst] at hv
            exact ih v hv
      · rw [if_neg hlen] at hv
        exact ih v hv

/-- The fold scan of a concatenation reads the later part first. -/
theorem foldScanFrom_append (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (u v : List Bool)
    (s : FoldScan α) :
    foldScanFrom R alg (u ++ v) s = foldScanFrom R alg u (foldScanFrom R alg v s) :=
  List.foldr_append

/-- The projection carries the whole scan, not only one step. -/
theorem toScan_foldScanFrom (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (s : FoldScan α) :
    ∀ w : List Bool, toScan (foldScanFrom R alg w s) = R.scanFrom w (toScan s) :=
  List.rec rfl fun b v ih ↦ by
    rw [foldScanFrom_cons, toScan_foldScanStep, ih, scanFrom_cons]

/-- The projection of the fold scan from the initial state is the validity
scan. -/
theorem toScan_foldScanFinal (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    toScan (foldScanFinal R alg w) = R.scanFinal w :=
  toScan_foldScanFrom R alg ⟨[], [], true⟩ w

/-- A word shorter than a block only accumulates, as it does in the validity
scan. -/
theorem foldScanFrom_short (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (st : List α)
    (bs : List Bool) :
    ∀ u : List Bool, u.length + bs.length < R.width →
      foldScanFrom R alg u ⟨bs, st, true⟩ = ⟨u ++ bs, st, true⟩ :=
  List.rec (fun _ ↦ rfl)
    (fun b v ih hv ↦ by
      rw [foldScanFrom_cons, ih (by simp only [List.length_cons] at hv; omega),
        foldScanStep]
      dsimp only
      rw [if_neg (by
        simp only [List.length_cons, List.length_append] at hv ⊢
        omega)]
      rfl)

/-- Reading a symbol's block from a state with no incomplete block whose stack
begins with the symbol's arguments pops them and pushes the algebra applied to
them. -/
theorem foldScanFrom_code (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (i : Fin R.card)
    (vals : Fin (R.arity i) → α) (st : List α) :
    foldScanFrom R alg (R.code i) ⟨[], List.ofFn vals ++ st, true⟩ =
      ⟨[], alg i vals :: st, true⟩ := by
  obtain ⟨b, v, hcode⟩ : ∃ b v, R.code i = b :: v := by
    match hc : R.code i with
    | [] =>
      have hw := length_code R i
      rw [hc] at hw
      exact absurd hw.symm (Nat.ne_of_gt R.width_pos)
    | b :: v => exact ⟨b, v, rfl⟩
  have hw := length_code R i
  rw [hcode, List.length_cons] at hw
  have hofFn : (List.ofFn vals).length = R.arity i := List.length_ofFn
  have hle : R.arity i ≤ (List.ofFn vals ++ st).length := by
    rw [List.length_append, hofFn]
    omega
  rw [hcode, foldScanFrom_cons,
    foldScanFrom_short R alg (List.ofFn vals ++ st) [] v (by simp; omega),
    foldScanStep]
  simp only [List.append_nil]
  rw [if_pos (by rw [List.length_cons]; omega), ← hcode, symOf_decodeBits_code]
  dsimp only
  rw [dif_pos hle]
  refine FoldScan.ext rfl ?_ rfl
  refine congrArg₂ List.cons (congrArg (alg i) (funext fun d ↦ ?_))
    (List.drop_left' hofFn)
  have hd : d.val < (List.ofFn vals).length := by rw [hofFn]; exact d.isLt
  rw [List.getElem_append_left hd, List.getElem_ofFn]

/-- The fold scan of a family of spellings pushes one value per spelling, in
index order: the value of index zero ends on top. -/
theorem foldScanFrom_ofFn (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) :
    ∀ (n : ℕ) (f : Fin n → List Bool) (g : Fin n → α),
      (∀ (d : Fin n) (t : List α),
        foldScanFrom R alg (f d) ⟨[], t, true⟩ = ⟨[], g d :: t, true⟩) →
      ∀ st : List α,
        foldScanFrom R alg (List.ofFn f).flatten ⟨[], st, true⟩ =
          ⟨[], List.ofFn g ++ st, true⟩ :=
  Nat.rec
    (fun _ _ _ st ↦ by
      rw [List.ofFn_zero, List.flatten_nil, foldScanFrom_nil, List.ofFn_zero,
        List.nil_append])
    (fun _ ih f g hf st ↦ by
      rw [List.ofFn_succ, List.flatten_cons, foldScanFrom_append,
        ih (fun i ↦ f i.succ) (fun i ↦ g i.succ) (fun d t ↦ hf d.succ t) st,
        hf 0 (List.ofFn (fun i ↦ g i.succ) ++ st), List.ofFn_succ, List.cons_append])

/-- A spelling pushes one value: the fold of the term it spells, whatever the
stack before it. -/
theorem foldScanFrom_spell (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (t : R.Term)
    (st : List α) :
    foldScanFrom R alg (R.spell t) ⟨[], st, true⟩ =
      ⟨[], Term.fold R alg t :: st, true⟩ :=
  Term.induction
    (motive := fun t ↦ ∀ st : List α, foldScanFrom R alg (R.spell t) ⟨[], st, true⟩ =
      ⟨[], Term.fold R alg t :: st, true⟩)
    (fun i ch ih st ↦ by
      rw [spell_mk, foldScanFrom_append,
        foldScanFrom_ofFn R alg (R.arity i) (fun d ↦ R.spell (ch d))
          (fun d ↦ Term.fold R alg (ch d)) (fun d t ↦ ih d t) st,
        foldScanFrom_code R alg i (fun d ↦ Term.fold R alg (ch d)) st]
      rfl)
    t st

/-- The final state read as an `Option`: the value on top of the stack when the
scan ends live, with no incomplete block and exactly one pending subterm, and
absent otherwise. The three conditions are those of
`RankedAlphabet.validBool`, read on the stack's length rather than on a
count. -/
def foldOut (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    Option α :=
  if (foldScanFinal R alg w).live && (foldScanFinal R alg w).buf.isEmpty &&
      (foldScanFinal R alg w).stack.length == 1 then
    (foldScanFinal R alg w).stack.head?
  else none

/-- The condition `foldOut` tests is the recognizer's verdict. The projection
supplies it: the three fields the test reads are the three
`RankedAlphabet.validBool` reads, and `toScan` carries each. -/
theorem foldOut_cond (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    ((foldScanFinal R alg w).live && (foldScanFinal R alg w).buf.isEmpty &&
      (foldScanFinal R alg w).stack.length == 1) = R.validBool w := by
  rw [validBool, ← toScan_foldScanFinal R alg w, toScan]

/-- A spelling folds to the fold of the term it spells. -/
theorem foldOut_spell (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (t : R.Term) :
    foldOut R alg (R.spell t) = some (Term.fold R alg t) := by
  rw [foldOut, foldScanFinal, foldScanFrom_spell]
  rfl

/-- A word spelling no term folds to nothing: the condition `foldOut` tests is
the recognizer's verdict, which `RankedAlphabet.valid_iff_exists_spell` places
exactly at the spellings. -/
theorem foldOut_eq_none_of_not_valid (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool)
    (h : ¬ R.Valid w) : foldOut R alg w = none := by
  rw [foldOut, foldOut_cond]
  exact if_neg h

/-- The fold scan computes the decoding followed by the fold: the unique
algebra morphism out of the term algebra, read off the spelling. -/
theorem foldOut_eq (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    foldOut R alg w = (R.parse w).map (Term.fold R alg) := by
  match hp : R.parse w with
  | some t =>
    rw [Option.map_some]
    rw [← (parse_eq_some_iff R).mp hp]
    exact foldOut_spell R alg t
  | none =>
    rw [Option.map_none]
    refine foldOut_eq_none_of_not_valid R alg w fun hv ↦ ?_
    rw [valid_iff_isSome_parse, hp] at hv
    exact absurd hv (by simp)

/-- One step raises the alphabet's width times the pending count, plus the
incomplete block's length, by at most one. Every clause but the completing pop
leaves the count alone; the pop raises it by at most one, and the block it
consumes is worth the width. -/
theorem width_mul_depth_scanStep_le (R : RankedAlphabet) (b : Bool) (s : Scan) :
    R.width * (R.scanStep b s).depth + (R.scanStep b s).buf.length ≤
      R.width * s.depth + s.buf.length + 1 := by
  obtain ⟨buf, depth, live⟩ := s
  rw [scanStep]
  dsimp only
  cases live
  · dsimp only
    omega
  · dsimp only
    cases hc : decide ((b :: buf).length = R.width)
    · dsimp only
      simp only [List.length_cons]
      omega
    · dsimp only
      have hbw : buf.length + 1 = R.width := by
        have hd := of_decide_eq_true hc
        rw [List.length_cons] at hd
        omega
      cases R.arOf (decodeBits (b :: buf))
      · dsimp only
        simp only [List.length_nil]
        omega
      · rename_i r
        dsimp only
        cases decide (r ≤ depth)
        · dsimp only
          simp only [List.length_nil]
          omega
        · dsimp only
          have h2 : R.width * (depth - r + 1) ≤ R.width * (depth + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have h3 : R.width * (depth + 1) = R.width * depth + R.width :=
            Nat.mul_succ _ _
          simp only [List.length_nil]
          omega

/-- The incomplete block of the fold scan is the incomplete block of the
validity scan, the projection carrying it. -/
theorem buf_foldScanFinal (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    (foldScanFinal R alg w).buf = (R.scanFinal w).buf :=
  congrArg Scan.buf (toScan_foldScanFinal R alg w)

/-- The stack's height is the validity scan's pending count. -/
theorem length_stack_foldScanFinal (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    (foldScanFinal R alg w).stack.length = (R.scanFinal w).depth :=
  congrArg Scan.depth (toScan_foldScanFinal R alg w)

/-- The fold scan's incomplete block never fills. -/
theorem length_buf_foldScanFinal_lt (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    (foldScanFinal R alg w).buf.length < R.width := by
  rw [buf_foldScanFinal]
  exact length_buf_scanFinal_lt R w

/-- Two folds whose algebras commute with a map agree on results, up to that
map, on every input. This is the equivalence between two fold constructions at
different carriers: neither construction enters the statement, only the shared
specification `foldOut_eq` gives them. -/
theorem foldOut_map (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α)
    (algV : (i : Fin R.card) → (Fin (R.arity i) → β) → β) (e : α → β)
    (he : ∀ (i : Fin R.card) (g : Fin (R.arity i) → α),
      algV i (fun d ↦ e (g d)) = e (alg i g)) (w : List Bool) :
    foldOut R algV w = (foldOut R alg w).map e := by
  rw [foldOut_eq, foldOut_eq]
  match R.parse w with
  | none => rfl
  | some t =>
    rw [Option.map_some, Option.map_some, Term.fold_map R alg algV e he t]
    rfl

/-- The pending count rises only at a completed block, so the alphabet's width
times the count, plus the length of the incomplete block, is at most the word's
length. This sharpens `RankedAlphabet.depth_scanFinal_le_length` by the width:
the count is a number of symbols, not of bits. -/
theorem width_mul_depth_add_length_buf_scanFinal_le (R : RankedAlphabet)
    (w : List Bool) :
    R.width * (R.scanFinal w).depth + (R.scanFinal w).buf.length ≤ w.length :=
  List.rec (by simp only [scanFinal_nil, List.length_nil]; omega)
    (fun b v ih ↦ by
      rw [scanFinal_cons, List.length_cons]
      exact Nat.le_trans (width_mul_depth_scanStep_le R b (R.scanFinal v))
        (Nat.add_le_add_right ih 1)) w

/-- The pending count is at most the word's length divided by the block width,
in the multiplied form a state layout consumes. -/
theorem width_mul_depth_scanFinal_le (R : RankedAlphabet) (w : List Bool) :
    R.width * (R.scanFinal w).depth ≤ w.length :=
  Nat.le_trans (Nat.le_add_right _ _)
    (width_mul_depth_add_length_buf_scanFinal_le R w)

end Geb.CobhamFold

end
