/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.Tree.Ranked.Code
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Computability.Encoding

/-!
# The preorder encoding of ranked terms

A symbol is spelled by its block followed by its children's spellings, in
index order. The encoding is a bijection onto the words a single
right-to-left scan accepts, the scan carrying an incomplete block, the count
of pending subterms and a liveness flag.

The idea is that of prefix notation, in which a symbol is followed by exactly
as many operands as its arity. `RankedAlphabet.Binary` is the case of one
symbol of arity zero and one of arity two.

Validity is stated as three conditions, in the manner of mathlib's
`DyckWord`, whose fields `count_U_eq_count_D` and `count_D_le_count_U` play
the roles the pending count and the liveness flag play here, and in the
direction a single right-to-left pass carrying a counter can scan.
`valid_iff_scanFinal` adds a third, that the incomplete block is empty: at a
general width that condition is not implied by the other two, so stating
validity as only the first two, as `DyckWord` does, would be false here.

A `boundedRec` of a Cobham-style function algebra processes a list from its
far end, so in that reading a symbol's block is read before the blocks of its
children and the symbol is applied after them: prefix notation in list order
is postfix notation in processing order.

## Main definitions

* `RankedAlphabet.spell` — the encoding.
* `RankedAlphabet.decodeBlock`, `RankedAlphabet.parseChildren`,
  `RankedAlphabet.parseStep`, `RankedAlphabet.parseAux`,
  `RankedAlphabet.parse` — the fuel-bounded recursive-descent decoding.
* `RankedAlphabet.encoding` — the two as a `Computability.Encoding`.
* `RankedAlphabet.Scan`, `RankedAlphabet.scanStep`,
  `RankedAlphabet.scanFrom`, `RankedAlphabet.scanFinal` — the scan.
* `RankedAlphabet.validBool`, `RankedAlphabet.Valid` — what it accepts.
* `DecidablePred RankedAlphabet.Valid` — the instance deciding it.

## Main statements

* `RankedAlphabet.parse_spell` — the retraction law.
* `RankedAlphabet.parse_eq_some_iff` — the decoding inverts the encoding.
* `RankedAlphabet.spell_injective` — distinct terms have distinct spellings.
* `RankedAlphabet.valid_spell` — every spelling is valid.
* `RankedAlphabet.valid_iff_exists_spell` — the valid words are exactly the
  spellings.
* `RankedAlphabet.valid_iff_isSome_parse` — the descent decides validity.
* `RankedAlphabet.length_buf_scanFinal_of_live` — a live scan's incomplete
  block holds the word's length modulo the width.
* `RankedAlphabet.length_buf_scanFinal_lt` — the incomplete block never fills.
* `RankedAlphabet.depth_scanFinal_le_length` — the pending count is at most
  the word's length.
* `RankedAlphabet.valid_iff_scanFinal` — validity as three conditions on the
  final state.

## Implementation notes

`parseAux` recurses on an explicit `ℕ` bound rather than on its input: each
child is parsed from a remainder the previous call computes, which is not a
structural subterm. `parse` supplies the input's length, and `length_spell`
with `width_pos` shows that bound admits every word `spell` emits.

Fuel exhaustion is not a rejection mechanism of its own. Each `parseStep`
layer consumes a whole block, which `width_pos` makes at least one bit, so
the invariant that the fuel is at least the remaining length holds from
`parse`'s initial `w.length` down to wherever the descent stops. The
descent's own rejections are `decodeBlock`'s two — the input falls short of
a block, or the block spells no symbol — together with a child's failure and
the trailing input `parse` rejects.

`parseChildren` is a `Nat.rec` and `decodeBits` a `List.rec`, so neither has
generated equation lemmas; `parseChildren_succ` and `decodeBits_cons` are
stated for the rewrites that need them.

`scanStep` matches on `Bool` values and `Valid` is a `Bool` equation rather
than an equation of `Scan`. Both are required by kernel reduction: an equation
of `Scan` would be decided through a derived `DecidableEq`, which at a
symbolic fold leaves `decide` stuck on the instance rather than reducing it,
so `Scan` derives none. A decidable test is not itself the obstruction, as
`decodeBlock` shows by branching on one and reducing.

`exists_spell_append_of_live_of_buf_nil_of_one_le_depth` is likewise bounded
by an explicit `ℕ` and driven by `Nat.rec`. Its step applies the hypothesis
once per child of the head symbol, through
`exists_children_append_of_le_depth`, which takes that hypothesis as an
argument; every use sits at the same bound, so no well-founded recursion is
needed. The step splits off the word's leading block rather than its trailing
one: `spell` is prefix notation while the scan reads right to left, so the
head symbol's block is read last, from the state the scan of everything after
it leaves.

The base case ascribes `w.length ≤ 0` to `hzero` before appealing to `omega`:
`Nat.rec`'s base case presents the bound as `w.length ≤ Nat.zero`, and `omega`
treats the unreduced `Nat.zero` as an opaque atom, so the ascription at the
literal `0` is what makes the hypothesis usable.

`spell_injective` is derived from `Computability.Encoding.encode_injective`
through `encoding` rather than proved directly, the encoding and its descent
being exactly that structure's three fields.

## Tags

ranked alphabet, preorder, prefix notation, encoding, retraction, scan
-/

namespace RankedAlphabet

public section

/-- The preorder encoding: a symbol's block followed by its children's
spellings, in index order. -/
@[expose] def spell (R : RankedAlphabet) : R.Term → List Bool :=
  WType.elim (List Bool) fun x ↦ R.code x.1 ++ (List.ofFn x.2).flatten

@[simp] theorem spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    R.spell (Term.mk R i ch) = R.code i ++ (List.ofFn fun d ↦ R.spell (ch d)).flatten :=
  rfl

/-- A spelling's length is the alphabet's width times the term's node count,
so the input length is fuel enough for the descent to read anything `spell`
emits. -/
theorem length_spell (R : RankedAlphabet) (t : R.Term) :
    (R.spell t).length = R.width * t.size :=
  Term.induction (motive := fun t ↦ (R.spell t).length = R.width * t.size)
    (fun i ch ih ↦ by
      beta_reduce
      rw [spell_mk, List.length_append, length_code, size_mk, Nat.mul_add, Nat.mul_one,
        Nat.add_comm (R.width * _) R.width]
      congr 1
      rw [List.length_flatten, List.map_ofFn]
      simp only [Function.comp_def, ih]
      rw [show (List.ofFn fun x ↦ R.width * (ch x).size)
            = List.map (fun b ↦ R.width * b) (List.ofFn fun d ↦ (ch d).size) by
          rw [List.map_ofFn]; rfl, List.sum_map_mul_left, List.map_id']) t

/-- Read one block: the symbol it spells and the unconsumed remainder, absent
when the word is short of a block or the block spells no symbol. -/
@[expose] def decodeBlock (R : RankedAlphabet) (w : List Bool) :
    Option (Fin R.card × List Bool) :=
  if h : decodeBits (w.take R.width) < R.card ∧ R.width ≤ w.length then
    some (⟨decodeBits (w.take R.width), h.1⟩, w.drop R.width)
  else none

/-- Read `n` children in index order, delegating each to `child`. -/
@[expose] def parseChildren {R : RankedAlphabet}
    (child : List Bool → Option (R.Term × List Bool)) :
    (n : ℕ) → List Bool → Option ((Fin n → R.Term) × List Bool) :=
  Nat.rec (fun w ↦ some (Fin.elim0, w))
    fun _ ih w ↦
      match child w with
      | none => none
      | some (t, w₁) =>
        match ih w₁ with
        | none => none
        | some (f, w₂) => some (Fin.cons t f, w₂)

/-- `parseChildren` unfolded on a positive count. `parseChildren` is a bare
`Nat.rec`, for which Lean generates no equation lemma. -/
theorem parseChildren_succ {R : RankedAlphabet}
    (child : List Bool → Option (R.Term × List Bool)) (n : ℕ) (w : List Bool) :
    parseChildren child (n + 1) w =
      (match child w with
       | none => none
       | some (t, w₁) =>
         match parseChildren child n w₁ with
         | none => none
         | some (f, w₂) => some (Fin.cons t f, w₂)) := rfl

/-- One layer of the recursive descent: read one block, then as many children
as its symbol's arity. -/
@[expose] def parseStep (R : RankedAlphabet)
    (child : List Bool → Option (R.Term × List Bool)) (w : List Bool) :
    Option (R.Term × List Bool) :=
  match R.decodeBlock w with
  | none => none
  | some (i, rest) =>
    match parseChildren child (R.arity i) rest with
    | none => none
    | some (f, rest') => some (Term.mk R i f, rest')

/-- Recursive descent bounded by an explicit `ℕ`. -/
@[expose] def parseAux (R : RankedAlphabet) :
    ℕ → List Bool → Option (R.Term × List Bool) :=
  Nat.rec (fun _ ↦ none) fun _ ih ↦ R.parseStep ih

theorem parseAux_succ (R : RankedAlphabet) (f : ℕ) :
    R.parseAux (f + 1) = R.parseStep (R.parseAux f) := rfl

/-- The decoding, rejecting trailing input. -/
@[expose] def parse (R : RankedAlphabet) (w : List Bool) : Option R.Term :=
  match R.parseAux w.length w with
  | some (t, []) => some t
  | _ => none

/-- A block followed by anything is read as its own symbol, leaving what
follows. -/
theorem decodeBlock_code_append (R : RankedAlphabet) (i : Fin R.card)
    (rest : List Bool) : R.decodeBlock (R.code i ++ rest) = some (i, rest) := by
  have htake : (R.code i ++ rest).take R.width = R.code i := by
    rw [← length_code R i, List.take_left]
  have hdrop : (R.code i ++ rest).drop R.width = rest := by
    rw [← length_code R i, List.drop_left]
  have hlen : R.width ≤ (R.code i ++ rest).length := by
    rw [List.length_append, length_code]
    omega
  simp only [decodeBlock, htake, hdrop,
    dif_pos (show decodeBits (R.code i) < R.card ∧ R.width ≤ (R.code i ++ rest).length
      from ⟨by rw [decodeBits_code]; exact i.isLt, hlen⟩)]
  congr 1
  exact Prod.ext (Fin.val_injective (decodeBits_code R i)) rfl

/-- Reading `n` children off the concatenation of their spellings returns them
and the remainder. -/
theorem parseChildren_flatten (R : RankedAlphabet) {n : ℕ} (ch : Fin n → R.Term)
    (ih : ∀ d f rest, (ch d).size ≤ f →
      R.parseAux f (R.spell (ch d) ++ rest) = some (ch d, rest))
    (f : ℕ) (rest : List Bool) (hf : ∀ d, (ch d).size ≤ f) :
    parseChildren (R.parseAux f) n
      ((List.ofFn fun d ↦ R.spell (ch d)).flatten ++ rest) = some (ch, rest) := by
  refine Nat.rec (motive := fun n ↦ ∀ (ch : Fin n → R.Term),
    (∀ d f' rest', (ch d).size ≤ f' →
      R.parseAux f' (R.spell (ch d) ++ rest') = some (ch d, rest')) →
    (∀ d, (ch d).size ≤ f) →
    parseChildren (R.parseAux f) n
      ((List.ofFn fun d ↦ R.spell (ch d)).flatten ++ rest) = some (ch, rest))
    ?base ?step n ch ih hf
  · intro ch _ _
    simp only [List.ofFn_zero, List.flatten_nil, List.nil_append, parseChildren]
    exact congrArg (fun g ↦ some (g, rest)) (funext fun d ↦ d.elim0)
  · intro n ihn ch ihch hch
    rw [List.ofFn_succ, List.flatten_cons, List.append_assoc, parseChildren_succ,
      ihch 0 f _ (hch 0)]
    simp only []
    rw [ihn (fun i ↦ ch i.succ) (fun d ↦ ihch d.succ) (fun d ↦ hch d.succ)]
    exact congrArg (fun g ↦ some (g, rest)) (Fin.cons_self_tail ch)

/-- The descent inverts the spelling on spelled input, given fuel at least the
term's node count, and returns the unconsumed remainder. -/
theorem parseAux_spell (R : RankedAlphabet) (t : R.Term) :
    ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      R.parseAux f (R.spell t ++ rest) = some (t, rest) :=
  Term.induction
    (motive := fun t ↦ ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      R.parseAux f (R.spell t ++ rest) = some (t, rest))
    (fun i ch ih f rest hf ↦ by
      cases f with
      | zero => exact absurd hf (by rw [size_mk]; exact Nat.not_succ_le_zero _)
      | succ f =>
        rw [parseAux_succ, spell_mk, List.append_assoc, parseStep,
          decodeBlock_code_append]
        have hchild : ∀ d, (ch d).size ≤ f := by
          intro d
          rw [size_mk] at hf
          have := size_le_sum_ofFn ch d
          omega
        simp only []
        rw [parseChildren_flatten R ch ih f rest hchild]) t

/-- The retraction law: the descent recovers every term the encoding
spells. -/
theorem parse_spell (R : RankedAlphabet) (t : R.Term) :
    R.parse (R.spell t) = some t := by
  have hf : t.size ≤ (R.spell t).length := by
    rw [length_spell]
    exact Nat.le_mul_of_pos_left _ R.width_pos
  have h := parseAux_spell R t (R.spell t).length [] hf
  rw [List.append_nil] at h
  rw [parse, h]

/-- The encoding and its descent as a `Computability.Encoding` over the
alphabet `Bool`, whose remaining three fields they are. -/
@[expose] def encoding (R : RankedAlphabet) : Computability.Encoding R.Term where
  Γ := Bool
  encode := R.spell
  decode := R.parse
  decode_encode := parse_spell R

/-- Distinct terms have distinct spellings. -/
theorem spell_injective (R : RankedAlphabet) : Function.Injective R.spell :=
  (R.encoding).encode_injective

/-- Whatever a block read returns, it reads that symbol's block. -/
theorem decodeBlock_eq_some (R : RankedAlphabet) {w rest : List Bool}
    {i : Fin R.card} (h : R.decodeBlock w = some (i, rest)) :
    R.code i ++ rest = w := by
  rw [decodeBlock] at h
  split at h
  · rename_i hcond
    have heq := Option.some.inj h
    have hi : decodeBits (w.take R.width) = i.val :=
      congrArg (fun p ↦ (Prod.fst p).val) heq
    have hrest : w.drop R.width = rest := congrArg Prod.snd heq
    have hlen : (R.code i).length = (w.take R.width).length := by
      rw [length_code, List.length_take]
      omega
    have hcode : R.code i = w.take R.width := by
      refine List.ext_getElem hlen ?_
      intro n h₁ h₂
      rw [getElem_code_eq R i n h₁, ← hi,
        testBit_decodeBits (w.take R.width) n h₂]
    rw [hcode, ← hrest, List.take_append_drop]
  · contradiction

/-- Whatever `parseChildren` returns, it reads the concatenation of the
children's spellings. -/
theorem parseChildren_eq_some (R : RankedAlphabet) (f : ℕ)
    (ih : ∀ w t rest, R.parseAux f w = some (t, rest) → R.spell t ++ rest = w) :
    ∀ (n : ℕ) (w : List Bool) (g : Fin n → R.Term) (rest : List Bool),
      parseChildren (R.parseAux f) n w = some (g, rest) →
        (List.ofFn fun d ↦ R.spell (g d)).flatten ++ rest = w :=
  Nat.rec
    (fun w g rest h ↦ by
      simp only [parseChildren] at h
      have heq := Option.some.inj h
      have hw : w = rest := congrArg Prod.snd heq
      rw [List.ofFn_zero, List.flatten_nil, List.nil_append, hw])
    (fun n ihn w g rest h ↦ by
      rw [parseChildren_succ] at h
      split at h
      · contradiction
      · rename_i t w₁ h₁
        split at h
        · contradiction
        · rename_i g' w₂ h₂
          have heq := Option.some.inj h
          have hg : Fin.cons t g' = g := congrArg Prod.fst heq
          have hrest : w₂ = rest := congrArg Prod.snd heq
          subst hg
          rw [List.ofFn_succ, List.flatten_cons, List.append_assoc, ← hrest]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [ihn w₁ g' w₂ h₂, ih w t w₁ h₁])

/-- Whatever the descent reads, it reads a spelling. -/
theorem parseAux_eq_some (R : RankedAlphabet) :
    ∀ (f : ℕ) (w : List Bool) (t : R.Term) (rest : List Bool),
      R.parseAux f w = some (t, rest) → R.spell t ++ rest = w :=
  Nat.rec
    (fun _ _ _ h ↦ nomatch h)
    (fun f ih w t rest h ↦ by
      rw [parseAux_succ, parseStep] at h
      split at h
      · contradiction
      · rename_i i rest₁ hb
        split at h
        · contradiction
        · rename_i g rest₂ hc
          have heq := Option.some.inj h
          have ht : Term.mk R i g = t := congrArg Prod.fst heq
          have hrest : rest₂ = rest := congrArg Prod.snd heq
          subst ht
          rw [spell_mk, List.append_assoc, ← hrest,
            parseChildren_eq_some R f ih (R.arity i) rest₁ g rest₂ hc,
            decodeBlock_eq_some R hb])

/-- The descent succeeds exactly on the spellings, returning the term
spelled. -/
theorem parse_eq_some_iff (R : RankedAlphabet) {w : List Bool} {t : R.Term} :
    R.parse w = some t ↔ R.spell t = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ parse_spell R t⟩
  rw [parse] at h
  split at h
  · rename_i t' hp
    rw [← Option.some.inj h]
    simpa using parseAux_eq_some R w.length w t' [] hp
  · contradiction

/-- The state of the validity scan: the bits of an incomplete block, the
count of pending subterms, and whether the scan has failed. -/
@[ext] structure Scan where
  /-- The bits of an incomplete block, most recently read first. -/
  buf : List Bool
  /-- The count of pending subterms. -/
  depth : ℕ
  /-- Whether the scan has not yet failed. -/
  live : Bool

/-- One step of the scan, reading one bit. A failed state absorbs. An
incomplete block takes the bit; a complete one is decoded, and its symbol
pops its arity and pushes one, failing when the block spells no symbol or the
pending count is short of the arity. -/
@[expose] def scanStep (R : RankedAlphabet) (b : Bool) (s : Scan) : Scan :=
  match s.live with
  | false => s
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => ⟨b :: s.buf, s.depth, true⟩
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => ⟨[], s.depth, false⟩
      | some r =>
        match decide (r ≤ s.depth) with
        | false => ⟨[], s.depth, false⟩
        | true => ⟨[], s.depth - r + 1, true⟩

/-- The scan of a word from a given state. `foldr` reads the word's last bit
first, which is the processing order of a right-to-left scan. -/
@[expose] def scanFrom (R : RankedAlphabet) (w : List Bool) (s : Scan) : Scan :=
  w.foldr R.scanStep s

/-- The scan of a word from the initial state. -/
@[expose] def scanFinal (R : RankedAlphabet) (w : List Bool) : Scan :=
  R.scanFrom w ⟨[], 0, true⟩

/-- Whether a word spells a term: the scan ends live, with no incomplete
block and exactly one pending subterm. -/
@[expose] def validBool (R : RankedAlphabet) (w : List Bool) : Bool :=
  (R.scanFinal w).live && (R.scanFinal w).buf.isEmpty && (R.scanFinal w).depth == 1

/-- A word spells a term. -/
@[expose] def Valid (R : RankedAlphabet) (w : List Bool) : Prop :=
  R.validBool w = true

/-- `Valid` is a `Bool` equation, so membership is decidable. Instance search
does not unfold the `def`, so the instance is supplied. -/
instance (R : RankedAlphabet) : DecidablePred R.Valid :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

@[simp] theorem scanFrom_nil (R : RankedAlphabet) (s : Scan) :
    R.scanFrom [] s = s := rfl

@[simp] theorem scanFrom_cons (R : RankedAlphabet) (b : Bool) (w : List Bool)
    (s : Scan) : R.scanFrom (b :: w) s = R.scanStep b (R.scanFrom w s) := rfl

@[simp] theorem scanFinal_nil (R : RankedAlphabet) :
    R.scanFinal [] = ⟨[], 0, true⟩ := rfl

@[simp] theorem scanFinal_cons (R : RankedAlphabet) (b : Bool) (w : List Bool) :
    R.scanFinal (b :: w) = R.scanStep b (R.scanFinal w) := rfl

/-- The scan of a concatenation reads the later part first. -/
theorem scanFrom_append (R : RankedAlphabet) (u v : List Bool) (s : Scan) :
    R.scanFrom (u ++ v) s = R.scanFrom u (R.scanFrom v s) :=
  List.rec rfl (fun b w ih ↦ by rw [List.cons_append, scanFrom_cons, ih, scanFrom_cons]) u

/-- Failure absorbs: no further input restores a failed scan. -/
theorem scanFrom_not_live (R : RankedAlphabet) (u : List Bool) (s : Scan)
    (h : s.live = false) : (R.scanFrom u s).live = false :=
  List.rec h (fun b v ih ↦ by rw [scanFrom_cons, scanStep, ih]; exact ih) u

/-- A word shorter than a block only accumulates. -/
theorem scanFrom_short (R : RankedAlphabet) (d : ℕ) (bs : List Bool) :
    ∀ u : List Bool, u.length + bs.length < R.width →
      R.scanFrom u ⟨bs, d, true⟩ = ⟨u ++ bs, d, true⟩ :=
  List.rec (fun _ ↦ rfl)
    (fun b v ih hv ↦ by
      rw [scanFrom_cons, ih (by simp only [List.length_cons] at hv; omega), scanStep]
      simp only []
      rw [decide_eq_false (by
        simp only [List.length_cons, List.length_append] at hv ⊢
        omega)]
      rfl)

/-- Reading a symbol's block from a state with no incomplete block and at
least the symbol's arity pending pops that arity and pushes one. -/
theorem scanFrom_code (R : RankedAlphabet) (i : Fin R.card) (d : ℕ)
    (h : R.arity i ≤ d) :
    R.scanFrom (R.code i) ⟨[], d, true⟩ = ⟨[], d - R.arity i + 1, true⟩ := by
  obtain ⟨b, v, hcode⟩ : ∃ b v, R.code i = b :: v := by
    match hc : R.code i with
    | [] =>
      have hw := length_code R i
      rw [hc] at hw
      exact absurd hw.symm (Nat.ne_of_gt R.width_pos)
    | b :: v => exact ⟨b, v, rfl⟩
  have hw := length_code R i
  rw [hcode, List.length_cons] at hw
  rw [hcode, scanFrom_cons, scanFrom_short R d [] v (by simp; omega), scanStep]
  simp only [List.append_nil]
  rw [decide_eq_true (by rw [List.length_cons]; omega)]
  simp only []
  rw [← hcode, arOf_decodeBits_code]
  simp only []
  rw [decide_eq_true h]

/-- The scan of a list of spellings, each raising the pending count by one,
raises it by their number. -/
theorem scanFrom_flatten (R : RankedAlphabet) (ws : List (List Bool))
    (hw : ∀ u ∈ ws, ∀ d, R.scanFrom u ⟨[], d, true⟩ = ⟨[], d + 1, true⟩) (d : ℕ) :
    R.scanFrom ws.flatten ⟨[], d, true⟩ = ⟨[], d + ws.length, true⟩ :=
  List.rec (motive := fun l ↦ (∀ u ∈ l, ∀ d, R.scanFrom u ⟨[], d, true⟩ =
      ⟨[], d + 1, true⟩) → R.scanFrom l.flatten ⟨[], d, true⟩ = ⟨[], d + l.length, true⟩)
    (fun _ ↦ by simp only [List.flatten_nil, scanFrom_nil, List.length_nil, Nat.add_zero])
    (fun u l ih hl ↦ by
      rw [List.flatten_cons, scanFrom_append,
        ih (fun x hx ↦ hl x (List.mem_cons_of_mem u hx)),
        hl u List.mem_cons_self (d + l.length), List.length_cons]
      congr 1)
    ws hw

/-- A spelling raises the pending count by one, whatever the count before
it. -/
theorem scanFrom_spell (R : RankedAlphabet) (t : R.Term) (d : ℕ) :
    R.scanFrom (R.spell t) ⟨[], d, true⟩ = ⟨[], d + 1, true⟩ :=
  Term.induction
    (motive := fun t ↦ ∀ d, R.scanFrom (R.spell t) ⟨[], d, true⟩ = ⟨[], d + 1, true⟩)
    (fun i ch ih d ↦ by
      rw [spell_mk, scanFrom_append,
        scanFrom_flatten R _ (fun u hu e ↦ by
          obtain ⟨n, hn⟩ := List.mem_ofFn.mp hu
          exact hn ▸ ih n e) d,
        List.length_ofFn, scanFrom_code R i (d + R.arity i) (Nat.le_add_left _ _)]
      congr 1
      omega)
    t d

/-- Every spelling is valid. -/
theorem valid_spell (R : RankedAlphabet) (t : R.Term) : R.Valid (R.spell t) := by
  rw [Valid, validBool, scanFinal, scanFrom_spell R t 0]
  rfl

/-- The residue of a successor, in terms of the residue. Stated here rather
than taken from `Nat`'s division API for the reason `mod_two_mul` is: the
modulus is a variable, so `omega` cannot discharge it, and the lemmas of that
API which do state it depend on `Classical.choice`. -/
theorem add_one_mod (a n : ℕ) (hn : 0 < n) :
    (a + 1) % n = if a % n + 1 = n then 0 else a % n + 1 := by
  have hsplit : (a + 1) % n = (a % n + 1) % n := by
    conv_lhs => rw [← Nat.div_add_mod a n]
    rw [Nat.add_assoc, Nat.mul_add_mod]
  rw [hsplit]
  split
  · rename_i h
    rw [h, Nat.mod_self]
  · rename_i h
    have hr : a % n < n := Nat.mod_lt _ hn
    exact Nat.mod_eq_of_lt (by omega)

/-- A step leaving the scan live: the state before it was live, and the step
either accumulated the bit into an incomplete block or completed one, in
which case its symbol popped that symbol's arity and pushed one. -/
theorem scanStep_eq_of_live (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : (R.scanStep b s).live = true) :
    s.live = true ∧
      (((b :: s.buf).length ≠ R.width ∧ R.scanStep b s = ⟨b :: s.buf, s.depth, true⟩) ∨
        ∃ r, (b :: s.buf).length = R.width ∧
          R.arOf (decodeBits (b :: s.buf)) = some r ∧ r ≤ s.depth ∧
          R.scanStep b s = ⟨[], s.depth - r + 1, true⟩) := by
  cases hlive : s.live with
  | false =>
    simp only [scanStep, hlive] at h
    exact Bool.noConfusion h
  | true =>
    refine ⟨rfl, ?_⟩
    cases hc : decide ((b :: s.buf).length = R.width) with
    | false =>
      refine Or.inl ⟨of_decide_eq_false hc, ?_⟩
      simp only [scanStep, hlive, hc]
    | true =>
      cases har : R.arOf (decodeBits (b :: s.buf)) with
      | none =>
        simp only [scanStep, hlive, hc, har] at h
        exact Bool.noConfusion h
      | some r =>
        cases hle : decide (r ≤ s.depth) with
        | false =>
          simp only [scanStep, hlive, hc, har, hle] at h
          exact Bool.noConfusion h
        | true =>
          exact Or.inr ⟨r, of_decide_eq_true hc, rfl, of_decide_eq_true hle, by
            simp only [scanStep, hlive, hc, har, hle]⟩

/-- A live scan's incomplete block holds the word's length modulo the width:
block boundaries align with the word's right end. -/
theorem length_buf_scanFinal_of_live (R : RankedAlphabet) :
    ∀ w : List Bool, (R.scanFinal w).live = true →
      (R.scanFinal w).buf.length = w.length % R.width :=
  List.rec (fun _ ↦ by simp only [scanFinal_nil, List.length_nil, Nat.zero_mod])
    (fun b v ih hlive ↦ by
      rw [scanFinal_cons] at hlive ⊢
      obtain ⟨hv, hcase⟩ := scanStep_eq_of_live R b (R.scanFinal v) hlive
      have ihv := ih hv
      rcases hcase with ⟨hne, heq⟩ | ⟨r, hlen, _, _, heq⟩
      · simp only [heq, List.length_cons] at hne ⊢
        rw [ihv] at hne
        rw [ihv, add_one_mod _ _ R.width_pos, if_neg hne]
      · simp only [List.length_cons] at hlen
        rw [ihv] at hlen
        simp only [heq, List.length_nil, List.length_cons]
        rw [add_one_mod _ _ R.width_pos, if_pos hlen])

/-- The incomplete block never fills, whether or not the scan has failed.
Stated unconditionally, which is the form a bitstring layout of the state
consumes; the `List.rec` below establishes the live and failed cases at once
rather than through `length_buf_scanFinal_of_live`. -/
theorem length_buf_scanFinal_lt (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).buf.length < R.width :=
  List.rec R.width_pos
    (fun b v ih ↦ by
      rw [scanFinal_cons, scanStep]
      cases (R.scanFinal v).live
      · exact ih
      · simp only []
        cases hc : decide ((b :: (R.scanFinal v).buf).length = R.width)
        · simp only [List.length_cons] at hc ⊢
          have := of_decide_eq_false hc
          omega
        · simp only []
          cases R.arOf (decodeBits (b :: (R.scanFinal v).buf))
          · exact R.width_pos
          · simp only []
            cases decide (_ ≤ (R.scanFinal v).depth) <;> exact R.width_pos) w

/-- The pending count is at most the word's length: every clause but the pop
leaves it alone, and the pop raises it by at most one. -/
theorem depth_scanFinal_le_length (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).depth ≤ w.length :=
  List.rec (Nat.le_refl 0)
    (fun b v ih ↦ by
      have hlen : (b :: v).length = v.length + 1 := rfl
      rw [scanFinal_cons, scanStep]
      cases (R.scanFinal v).live
      · simp only []
        omega
      · simp only []
        cases decide ((b :: (R.scanFinal v).buf).length = R.width)
        · simp only []
          omega
        · simp only []
          cases R.arOf (decodeBits (b :: (R.scanFinal v).buf))
          · simp only []
            omega
          · simp only []
            cases decide (_ ≤ (R.scanFinal v).depth)
            · simp only []
              omega
            · simp only []
              omega) w

/-- Validity as the three conditions on the final state, which is the form a
statement about the state word consumes. The two directions take different
routes: the forward one splits `validBool`'s conjunction and reads each
component, and the backward one closes by reduction once the fields are
substituted. -/
theorem valid_iff_scanFinal (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ ((R.scanFinal w).live = true ∧ (R.scanFinal w).buf = [] ∧
      (R.scanFinal w).depth = 1) := by
  constructor
  · intro hv
    have hb : ((R.scanFinal w).live && (R.scanFinal w).buf.isEmpty &&
        ((R.scanFinal w).depth == 1)) = true := hv
    rw [Bool.and_eq_true, Bool.and_eq_true] at hb
    exact ⟨hb.1.1, List.isEmpty_iff.mp hb.1.2, of_decide_eq_true hb.2⟩
  · intro hf
    change ((R.scanFinal w).live && (R.scanFinal w).buf.isEmpty &&
      ((R.scanFinal w).depth == 1)) = true
    rw [hf.1, hf.2.1, hf.2.2]
    rfl

/-- The converse of `scanFrom_code`: a live scan over a full block exhibits
that block as a symbol's code. -/
theorem exists_code_of_scanFrom_live (R : RankedAlphabet) (blk : List Bool)
    (s : Scan) (hlen : blk.length = R.width) (hbuf : s.buf = [])
    (hs : s.live = true) (h : (R.scanFrom blk s).live = true) :
    ∃ i : Fin R.card, R.code i = blk ∧ R.arity i ≤ s.depth ∧
      R.scanFrom blk s = ⟨[], s.depth - R.arity i + 1, true⟩ := by
  obtain ⟨sbuf, sdepth, slive⟩ := s
  simp only at hbuf hs
  subst hbuf
  subst hs
  obtain ⟨b, v, hblk⟩ : ∃ b v, blk = b :: v := by
    match hb : blk with
    | [] =>
      rw [List.length_nil] at hlen
      exact absurd hlen.symm (Nat.ne_of_gt R.width_pos)
    | b :: v => exact ⟨b, v, rfl⟩
  subst hblk
  have hshort : v.length + ([] : List Bool).length < R.width := by
    rw [List.length_cons] at hlen
    simp only [List.length_nil]
    omega
  rw [scanFrom_cons, scanFrom_short R sdepth [] v hshort, List.append_nil] at h ⊢
  obtain ⟨-, hcase⟩ := scanStep_eq_of_live R b ⟨v, sdepth, true⟩ h
  simp only at hcase
  rcases hcase with ⟨hne, -⟩ | ⟨r, -, har, hle, heq⟩
  · exact absurd hlen hne
  · rw [arOf] at har
    split at har
    · rename_i hlt
      have hr : R.arity ⟨decodeBits (b :: v), hlt⟩ = r := Option.some.inj har
      refine ⟨⟨decodeBits (b :: v), hlt⟩, ?_, hr ▸ hle, ?_⟩
      · refine List.ext_getElem (by rw [length_code, hlen]) ?_
        intro n h₁ h₂
        rw [getElem_code_eq R _ n h₁, testBit_decodeBits (b :: v) n h₂]
      · rw [hr, heq]
    · exact absurd har (by simp)

/-- A live scan with no incomplete block and nothing pending has read
nothing. -/
theorem eq_nil_of_live_of_buf_nil_of_depth_eq_zero (R : RankedAlphabet)
    (w : List Bool) (hlive : (R.scanFinal w).live = true)
    (hbuf : (R.scanFinal w).buf = []) (hd : (R.scanFinal w).depth = 0) : w = [] := by
  match w with
  | [] => rfl
  | b :: v =>
    rw [scanFinal_cons] at hlive hbuf hd
    obtain ⟨-, hcase⟩ := scanStep_eq_of_live R b (R.scanFinal v) hlive
    rcases hcase with ⟨-, heq⟩ | ⟨r, -, -, -, heq⟩
    · rw [heq] at hbuf
      exact absurd hbuf (by simp)
    · rw [heq] at hd
      exact absurd hd (by simp)

/-- Reading off as many complete subterms as the pending count allows: a live
scan with no incomplete block and at least `k` pending subterms has `k`
spellings as a prefix. The extraction of one subterm is the hypothesis `ih`,
at the same bound, as in `parseChildren_flatten`. -/
theorem exists_children_append_of_le_depth (R : RankedAlphabet) (n : ℕ)
    (ih : ∀ w : List Bool, w.length ≤ n → (R.scanFinal w).live = true →
      (R.scanFinal w).buf = [] → 1 ≤ (R.scanFinal w).depth →
        ∃ t rest, R.spell t ++ rest = w ∧ (R.scanFinal rest).live = true ∧
          (R.scanFinal rest).buf = [] ∧
          (R.scanFinal rest).depth + 1 = (R.scanFinal w).depth) :
    ∀ (k : ℕ) (v : List Bool), v.length ≤ n → (R.scanFinal v).live = true →
      (R.scanFinal v).buf = [] → k ≤ (R.scanFinal v).depth →
        ∃ (ch : Fin k → R.Term) (rest : List Bool),
          (List.ofFn fun d ↦ R.spell (ch d)).flatten ++ rest = v ∧
          (R.scanFinal rest).live = true ∧ (R.scanFinal rest).buf = [] ∧
          (R.scanFinal rest).depth + k = (R.scanFinal v).depth :=
  Nat.rec
    (fun v _ hlive hbuf _ ↦
      ⟨Fin.elim0, v, by simp only [List.ofFn_zero, List.flatten_nil, List.nil_append],
        hlive, hbuf, rfl⟩)
    (fun k ihk v hv hlive hbuf hk ↦ by
      obtain ⟨t, v₁, ht, hlive₁, hbuf₁, hd₁⟩ := ih v hv hlive hbuf (by omega)
      have hv₁ : v₁.length ≤ n := by
        have hle : v₁.length ≤ v.length := by rw [← ht, List.length_append]; omega
        omega
      obtain ⟨ch, rest, hch, hlive₂, hbuf₂, hd₂⟩ :=
        ihk v₁ hv₁ hlive₁ hbuf₁ (by omega)
      refine ⟨Fin.cons t ch, rest, ?_, hlive₂, hbuf₂, by omega⟩
      rw [List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [List.flatten_cons, List.append_assoc, hch, ht])

/-- A word whose scan is live, carries no incomplete block and leaves at least
one subterm pending has a complete spelling as a prefix. -/
theorem exists_spell_append_of_live_of_buf_nil_of_one_le_depth (R : RankedAlphabet) :
    ∀ (n : ℕ) (w : List Bool), w.length ≤ n →
      (R.scanFinal w).live = true → (R.scanFinal w).buf = [] →
      1 ≤ (R.scanFinal w).depth →
        ∃ t rest, R.spell t ++ rest = w ∧
          (R.scanFinal rest).live = true ∧ (R.scanFinal rest).buf = [] ∧
          (R.scanFinal rest).depth + 1 = (R.scanFinal w).depth :=
  Nat.rec
    (fun w hw _ _ hd ↦ by
      have hzero : w.length ≤ 0 := hw
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact absurd hd (by simp))
    (fun n ihn w hw hlive hbuf hd ↦ by
      have hmod : w.length % R.width = 0 := by
        rw [← length_buf_scanFinal_of_live R w hlive, hbuf, List.length_nil]
      have hne : w ≠ [] := by
        intro hcon
        subst hcon
        exact absurd hd (by simp)
      have hwidth : R.width ≤ w.length := by
        by_contra hcon
        rw [Nat.mod_eq_of_lt (Nat.lt_of_not_le hcon)] at hmod
        exact hne (List.eq_nil_of_length_eq_zero hmod)
      obtain ⟨blk, rest, hsplit, hlenblk⟩ :
          ∃ blk rest, blk ++ rest = w ∧ blk.length = R.width :=
        ⟨w.take R.width, w.drop R.width, List.take_append_drop _ _,
          by rw [List.length_take]; omega⟩
      have hlensum : R.width + rest.length = w.length := by
        rw [← hsplit, List.length_append, hlenblk]
      have hscan : R.scanFinal w = R.scanFrom blk (R.scanFinal rest) := by
        conv_lhs => rw [← hsplit]
        rw [scanFinal, scanFrom_append]
        rfl
      have hlive' : (R.scanFinal rest).live = true := by
        cases hc : (R.scanFinal rest).live with
        | true => rfl
        | false =>
          rw [hscan, scanFrom_not_live R blk _ hc] at hlive
          exact Bool.noConfusion hlive
      have hbuf' : (R.scanFinal rest).buf = [] := by
        refine List.eq_nil_of_length_eq_zero ?_
        rw [length_buf_scanFinal_of_live R rest hlive',
          ← Nat.add_mod_left R.width rest.length, hlensum]
        exact hmod
      obtain ⟨i, hcode, hari, hstep⟩ :=
        exists_code_of_scanFrom_live R blk (R.scanFinal rest) hlenblk hbuf' hlive'
          (by rw [← hscan]; exact hlive)
      obtain ⟨ch, rest', hch, hlive'', hbuf'', hd''⟩ :=
        exists_children_append_of_le_depth R n ihn (R.arity i) rest
          (by have := R.width_pos; omega) hlive' hbuf' hari
      refine ⟨Term.mk R i ch, rest', ?_, hlive'', hbuf'', ?_⟩
      · rw [spell_mk, hcode, List.append_assoc, hch, hsplit]
      · rw [hscan, hstep]
        simp only []
        omega)

/-- Every valid word is a spelling: the converse of `valid_spell`. -/
theorem exists_spell_of_valid (R : RankedAlphabet) {w : List Bool} (h : R.Valid w) :
    ∃ t, R.spell t = w := by
  rw [Valid, validBool] at h
  simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
  obtain ⟨⟨hlive, hbuf⟩, hd⟩ := h
  obtain ⟨t, rest, he, hlive', hbuf', hd'⟩ :=
    exists_spell_append_of_live_of_buf_nil_of_one_le_depth R w.length w le_rfl
      hlive hbuf (by omega)
  have hz : (R.scanFinal rest).depth = 0 := by omega
  have hnil : rest = [] :=
    eq_nil_of_live_of_buf_nil_of_depth_eq_zero R rest hlive' hbuf' hz
  subst hnil
  exact ⟨t, by simpa using he⟩

/-- The encoding's image is exactly the valid words: the characterization the
recognizer's correctness is stated against. -/
theorem valid_iff_exists_spell (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ ∃ t, R.spell t = w :=
  ⟨exists_spell_of_valid R, fun ⟨t, ht⟩ ↦ ht ▸ valid_spell R t⟩

/-- The descent decides validity: a word is valid exactly when `parse`
accepts it. -/
theorem valid_iff_isSome_parse (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ (R.parse w).isSome := by
  rw [valid_iff_exists_spell]
  refine ⟨fun ⟨t, ht⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← ht, parse_spell]
    rfl
  · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨t, (parse_eq_some_iff R).mp ht⟩

end

end RankedAlphabet
