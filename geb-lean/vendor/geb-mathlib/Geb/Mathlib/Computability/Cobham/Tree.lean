/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Basic
public import Geb.Mathlib.Data.Tree.Preorder

/-!
# The preorder stack scan in Cobham's class

An expression of `C` computing, in a single right-to-left pass over a
bitstring, the stack depth of the word read as the preorder spelling of a
binary tree, together with the verdict of `BinTree.ok`. The two are carried in
one recursive value, told apart by its head: while no node bit has been read
below depth two the value is the depth in unary offset by one, so its head is
`true`; once one has been, the value is `[false]`, which the node step
reproduces, that value's two predecessors being empty. Each bit is read once.

The recursion is a `boundedRec` node, so admissibility requires a bound: the
scan's value is never longer than the recursion variable by more than one bit,
which the successor `S₁` expresses as a term of arity one. That is the side
condition of bounded recursion on notation [Cobham1965], and discharging it is
what places the scan in `C` rather than merely in the syntax `sig` describes.

The one-test on the scan's predecessor is the recognizer, correct against the
`Valid` predicate of the encoding. Composed with
`BinTree.valid_iff_exists_print`, `isTreeSem_eq_singleton_iff_exists_print`
states that an expression of `C` accepts exactly the spellings of trees.
`isTreeSem_eq_ite` pins its value on the rejecting branch as well: the two
`iff` statements alone do not imply it, since a recognizer returning
`[false]` rather than `[]` on a rejected word would satisfy both while
disagreeing with `isTreeSem_eq_ite` there, so the correctness the latter
states is a property of the function and not only of the accepted set.

`isTree_smashFree` places `isTree` in the subalgebra `SmashFree` names,
`[ε, I, s₀, s₁, ∗; COMP, BRN]`; with [Strahm2003] Theorem 1(2), deciding
`BinTree.Valid` is computable simultaneously in polynomial time and linear
space.

## Main definitions

* `Cobham.zeroAt`, `Cobham.oneAt`, `Cobham.falseAt` — the empty bitstring and
  the one-bit strings `[true]` and `[false]`, at an arbitrary arity.
* `Cobham.inc` — prepending `true`, of arity one.
* `Cobham.predPred` — the argument with two bits dropped, of arity one.
* `Cobham.combFalseStep`, `Cobham.combTrueStep` — the leaf step and the node
  step of the scan, of arity two.
* `Cobham.comb` — the stack depth and the underflow verdict in one value, of
  arity one.
* `Cobham.eqOneInner` — whether the predecessor of the argument is empty, of
  arity one.
* `Cobham.eqOne` — whether a bitstring has length one, of arity one.
* `Cobham.isTree` — the recognizer, of arity one.
* `Cobham.combSem`, `Cobham.eqOneSem`, `Cobham.isTreeSem` — the meaning of
  the scan, the length test and the recognizer at its arity, over which
  every statement of the module is stated.

Every expression is given as a raw tree `…Raw` and as the expression `…` of `C`
carrying admissibility. The ascription `…Of` at the reduced arity is given
for the scan, the length test and the recognizer, matching the interface
`BellantoniCook.comb`, `BellantoniCook.eqOne` and `BellantoniCook.isTree`
present, and for an expression whose reduced arity a proof reads.

## Main statements

* `Cobham.combSem_nil`, `Cobham.combSem_cons_false`,
  `Cobham.combSem_cons_true` — the scan unfolded at each constructor of the
  recursion variable, with the recursive value exposed.
* `Cobham.combSem_eq` — the scan computes `BinTree.depth` in unary, offset by
  one, while `BinTree.ok` holds, and `[false]` once it has failed.
* `Cobham.combSem_eq_eval`, `Cobham.isTreeSem_eq_eval` — the meaning read at
  the raw tree is the meaning the expression of `C` carries.
* `Cobham.eqOneSem_env` — the one-test at an arbitrary environment is the
  test at the canonical one.
* `Cobham.eqOneSem_eq` — `eqOne` accepts exactly the bitstrings of length
  one.
* `Cobham.isTreeSem_apply` — one step of the recognizer: the one-test on
  the scan's predecessor.
* `Cobham.isTreeSem_eq_ite` — the recognizer's value on both branches:
  `[true]` on a word satisfying `BinTree.Valid` and `[]` on every other.
* `Cobham.isTreeSem_eq_singleton_iff_valid` — `isTree` accepts exactly the
  words satisfying `BinTree.Valid`.
* `Cobham.isTreeSem_eq_singleton_iff_exists_print` — equivalently, exactly
  the spellings of trees.
* `Cobham.isTree_smashFree` — the recognizer lies in the subalgebra
  `SmashFree` names.

## Implementation notes

Each raw tree is named apart from the expression built on it because instance
search finds `Decidable (sig.WValid w)` when `w` is a constant but not when it
is a literal `WType.mk` application, so `decide` discharges admissibility only
of a named tree. `zeroAtRaw`, `oneAtRaw` and `falseAtRaw` carry a free arity,
at which `decide` does not apply; their admissibility is the pair of an
`Unit ⊕ Fin m` case analysis and the `funext` that the index condition asks
for. The admissibility of an expression embedding `pred` or `cond` reuses that
expression's own component rather than repeating its proof.

`combSem` is the meaning read at the raw tree rather than at `comb`.
`Cobham.eval` asks only for admissibility as a `sig`-tree, not for the
recursion bound, so the scan is characterized by `combSem_eq` before the
expression carrying that bound exists. The bound is then that characterization
together with `BinTree.depth_le_length`: the value is `[false]`, of length one,
or the depth in unary offset by one, and the depth never exceeds the word
length, while the bound child `S₁` returns one bit more than the recursion
variable. Reading `comb` back through `C.eval` returns `combSem`, both being
the same transport along `fst_eval`, which `combSem_eq_eval` states and
`isTreeSem_eq_eval` states for the recognizer.

That bound is a bound on the value `combSem` produces at each step, not a
bound on the cost of evaluating the expression that computes it: nothing in
this module measures a number of reduction steps or an amount of space
consumed while doing so. `isTree_smashFree` states only that `isTree` avoids
the `smash` generator; the polynomial-time, linear-space reading of that
membership is [Strahm2003] Theorem 1(2), cited and not reproved here.

`cond` and `pred` are `boundedRec` nodes in this algebra rather than
generators, so a step's meaning reduces only once the value it scrutinizes is
in constructor form: `combSem_cons_false` and `combSem_cons_true` are therefore
not definitional, and each is proved by rewriting the scan to the step's own
application at the recursive value, generalizing that value, and matching on
it. The node step's guard drops two bits through two `pred` nodes, each of
which peels a bit only at a literal, so the match reaches the fourth
constructor layer of the value.

`combSem` names the meaning at the reduced arity, so that rewriting under it
type-checks. A meaning taken through the `Sigma` projection instead has a type
headed by that projection rather than by an arrow, and `rw` under it fails as
not type-correct at `implicit` transparency.

`eqOne` and `isTree` are `comp` compositions of `pred`, `cond` and `comb`,
carrying no `boundedRec` node of their own, so each admissibility obligation
is discharged by the anonymous constructor pairing the node's own condition,
vacuous at a `comp`, with a case analysis over its children, reusing the
embedded subexpression's own `RecBounded` component rather than repeating its
proof. Unlike a primitive predecessor shape, `pred` here is itself a
`boundedRec` node (`predRaw`), so its value on the scan's result does not
reduce on a symbolic word: `isTreeSem_apply` is proved, as
`combSem_cons_false` and `combSem_cons_true` are, by rewriting to the
composition's own application, generalizing the scan's value, and matching
on it, rather than by `rfl`.

## References

* [Cobham1965]
* [Strahm2003]

## Tags

Cobham, bounded recursion on notation, binary tree, preorder, stack depth,
smash-free, polynomial time, linear space
-/

namespace Cobham

public section

/-- The empty bitstring at an arbitrary arity. -/
@[expose] def zeroAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 0) fun d ↦
    match d with
    | .inl () => WType.mk .zero Fin.elim0
    | .inr i => i.elim0

/-- The empty bitstring as an expression of arity `n`. -/
@[expose] def zeroAt (n : ℕ) : C :=
  ⟨⟨zeroAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr i => i.elim0,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr i => i.elim0⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr i => i.elim0⟩⟩

/-- `zeroAt n` at its declared arity. -/
@[expose] def zeroAtOf (n : ℕ) : COf n := ⟨zeroAt n, rfl⟩

/-- The one-bit string `[true]` at an arbitrary arity. -/
@[expose] def oneAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ true) Fin.elim0
    | .inr _ => zeroAtRaw n

/-- The one-bit string `[true]` as an expression of arity `n`. -/
@[expose] def oneAt (n : ℕ) : C :=
  ⟨⟨oneAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr _ => (zeroAt n).1.2,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr _ => rfl⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => (zeroAt n).2⟩⟩

/-- `oneAt n` at its declared arity. -/
@[expose] def oneAtOf (n : ℕ) : COf n := ⟨oneAt n, rfl⟩

/-- The one-bit string `[false]` at an arbitrary arity. -/
@[expose] def falseAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ false) Fin.elim0
    | .inr _ => zeroAtRaw n

/-- The one-bit string `[false]` as an expression of arity `n`. -/
@[expose] def falseAt (n : ℕ) : C :=
  ⟨⟨falseAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr _ => (zeroAt n).1.2,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr _ => rfl⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => (zeroAt n).2⟩⟩

/-- `falseAt n` at its declared arity. -/
@[expose] def falseAtOf (n : ℕ) : COf n := ⟨falseAt n, rfl⟩

/-- Prepend `true` to the sole argument. -/
@[expose] def incRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ true) Fin.elim0
    | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- Prepending `true`, as an expression of arity one. -/
@[expose] def inc : C :=
  ⟨⟨incRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩

/-- `inc` at its declared arity. -/
@[expose] def incOf : COf 1 := ⟨inc, rfl⟩

/-- The sole argument with two bits dropped. It is empty exactly when the
argument is the failure flag, whose two predecessors truncate to the empty
bitstring, or a depth below two. -/
@[expose] def predPredRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => predRaw
    | .inr _ =>
      WType.mk (.comp 1 1) fun e ↦
        match e with
        | .inl () => predRaw
        | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- Dropping two bits, as an expression of arity one. -/
@[expose] def predPred : C :=
  ⟨⟨predPredRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => pred.1.2
      | .inr _ =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩⟩

/-- `predPred` at its declared arity. -/
@[expose] def predPredOf : COf 1 := ⟨predPred, rfl⟩

/-- The leaf step: push a level onto a live value, whose head is `true`, and
return the failure flag on a value that is empty or has head `false`. The
recursive value is the second of the step's two arguments. -/
@[expose] def combFalseStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 2 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.proj 2 1) Fin.elim0, falseAtRaw 2,
        WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => incRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0),
        falseAtRaw 2] i

/-- The leaf step as an expression of arity two. -/
@[expose] def combFalseStep : C :=
  ⟨⟨combFalseStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr 1 => (falseAt 2).2
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => inc.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 => (falseAt 2).2⟩⟩

/-- `combFalseStep` at its declared arity. -/
@[expose] def combFalseStepOf : COf 2 := ⟨combFalseStep, rfl⟩

/-- The node step: pop a level when at least two remain, and return the failure
flag otherwise. An existing failure propagates, its guard being empty. -/
@[expose] def combTrueStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 2 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => predPredRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0),
        falseAtRaw 2,
        WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0),
        WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0)] i

/-- The node step as an expression of arity two. -/
@[expose] def combTrueStep : C :=
  ⟨⟨combTrueStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => predPred.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 1 => (falseAt 2).2
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩⟩

/-- `combTrueStep` at its declared arity. -/
@[expose] def combTrueStepOf : COf 2 := ⟨combTrueStep, rfl⟩

/-- The raw tree of the scan. The base is `[true]`, the empty bitstring having
depth zero and satisfying `ok`; the bound is `S₁`, whose value is one longer
than the recursion variable. -/
@[expose] def combRaw : sig.toPFunctor.W :=
  WType.mk (.boundedRec 0)
    ![oneAtRaw 0, combFalseStepRaw, combTrueStepRaw, WType.mk (.succ true) Fin.elim0]

/-- The scan's meaning at its arity, taken at the raw tree. `Cobham.eval`
asks only for admissibility as a `sig`-tree, so the scan is characterized
before the expression carrying its recursion bound is formed. -/
@[expose] def combSem : Sem 1 :=
  transport (fst_eval ⟨combRaw, by decide⟩) (eval ⟨combRaw, by decide⟩).2

/-- The scan's value on the empty bitstring: depth zero, offset by one. -/
theorem combSem_nil : combSem ![[]] = [true] := rfl

/-- A leaf bit pushes a level onto a live value, and is absorbed by a
failure. -/
theorem combSem_cons_false (v : List Bool) :
    combSem ![false :: v] =
      (match combSem ![v] with
       | [] => [false]
       | true :: _ => true :: combSem ![v]
       | false :: _ => [false]) := by
  change transport combFalseStepOf.2 combFalseStepOf.1.eval ![v, combSem ![v]] = _
  generalize combSem ![v] = r
  match r with
  | [] | true :: _ | false :: _ => rfl

/-- A node bit pops a level when at least two remain, and fails otherwise. The
guard is the value with two bits dropped, so a failure, whose two predecessors
are empty, propagates. -/
theorem combSem_cons_true (v : List Bool) :
    combSem ![true :: v] =
      (match (combSem ![v]).tail.tail with
       | [] => [false]
       | true :: _ => (combSem ![v]).tail
       | false :: _ => (combSem ![v]).tail) := by
  change transport combTrueStepOf.2 combTrueStepOf.1.eval ![v, combSem ![v]] = _
  generalize combSem ![v] = r
  match r with
  | [] => rfl
  | [c] => cases c <;> rfl
  | c :: d :: w =>
    cases c <;> cases d <;> (match w with | [] | true :: _ | false :: _ => rfl)

/-- The scan computes the stack depth in unary, offset by one, while `ok`
holds, and the absorbing value `[false]` once it has failed. -/
theorem combSem_eq (w : List Bool) :
    combSem ![w] =
      if BinTree.ok w then List.replicate (BinTree.depth w + 1) true
      else [false] := by
  refine List.rec (motive := fun u ↦ combSem ![u] =
    if BinTree.ok u then List.replicate (BinTree.depth u + 1) true else [false])
    rfl ?_ w
  intro b v ih
  cases hok : BinTree.ok v
  · have hv : combSem ![v] = [false] := by rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, BinTree.ok_cons_false, hok]
      rfl
    · rw [combSem_cons_true, hv, BinTree.ok_cons_true, hok]
      rfl
  · have hv : combSem ![v] = List.replicate (BinTree.depth v + 1) true := by
      rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, BinTree.ok_cons_false, hok,
        BinTree.depth_cons_false]
      rfl
    · rw [combSem_cons_true, hv, BinTree.ok_cons_true, hok,
        BinTree.depth_cons_true]
      -- the guard's two predecessors reduce only on a numeral of at least that
      -- size, so the depth is split into constructor forms
      have hsplit : ∀ d : ℕ, d = 0 ∨ d = 1 ∨ ∃ m, d = m + 2 := fun d ↦
        match d with
        | 0 => Or.inl rfl
        | 1 => Or.inr (Or.inl rfl)
        | (m + 2) => Or.inr (Or.inr ⟨m, rfl⟩)
      obtain (h0 | h1 | ⟨m, hm⟩) := hsplit (BinTree.depth v)
      · rw [h0]; rfl
      · rw [h1]; rfl
      · rw [hm]; rfl

/-- The stack depth and the underflow verdict of a bitstring in one value. Its
recursion respects the bound because the value is `[false]`, of length one, or
the depth in unary offset by one, and the depth never exceeds the word length
(`BinTree.depth_le_length`), while the bound child `S₁` returns one bit more
than the recursion variable. -/
@[expose] def comb : C :=
  ⟨⟨combRaw, by decide⟩, by
    have hb : ∀ u : List Bool, (combSem ![u]).length ≤ u.length + 1 := by
      intro u
      rw [combSem_eq]
      cases BinTree.ok u
      · exact Nat.le_add_left 1 u.length
      · rw [if_pos rfl, List.length_replicate]
        exact Nat.succ_le_succ (BinTree.depth_le_length u)
    refine ⟨fun x ↦ ?_, ?_⟩
    · change _ ≤ (x 0).length + 1
      rw [(funext fun i ↦ i.elim0 : Fin.tail x = Fin.tail ![x 0])]
      exact hb (x 0)
    · refine fun b : Fin 4 ↦ ?_
      match b with
      | 0 => exact (oneAt 0).2
      | 1 => exact combFalseStep.2
      | 2 => exact combTrueStep.2
      | 3 => exact ⟨trivial, fun c ↦ c.elim0⟩⟩

/-- `comb` at its declared arity. -/
@[expose] def combOf : COf 1 := ⟨comb, rfl⟩

/-- The meaning `combSem` reads at the raw tree is the meaning `comb` carries:
the statements about the scan are statements about the member of `C` whose
recursion bound `comb` discharges. -/
theorem combSem_eq_eval : transport combOf.2 combOf.1.eval = combSem := rfl

/-- The inner conditional of `eqOne`: whether the predecessor of the argument
is empty. -/
@[expose] def eqOneInnerRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        oneAtRaw 1, zeroAtRaw 1, zeroAtRaw 1] i

/-- The inner conditional as an expression of arity one. -/
@[expose] def eqOneInner : C :=
  ⟨⟨eqOneInnerRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 1 => (oneAt 1).2
      | .inr 2 => (zeroAt 1).2
      | .inr 3 => (zeroAt 1).2⟩⟩

/-- `eqOneInner` at its declared arity. -/
@[expose] def eqOneInnerOf : COf 1 := ⟨eqOneInner, rfl⟩

/-- The raw tree of the one-test: the empty bitstring is not one, and
otherwise the argument is one exactly when its predecessor is empty. -/
@[expose] def eqOneRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.proj 1 0) Fin.elim0, zeroAtRaw 1, eqOneInnerRaw, eqOneInnerRaw] i

/-- Whether a bitstring has length one, as an expression of arity one. -/
@[expose] def eqOne : C :=
  ⟨⟨eqOneRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr 1 => (zeroAt 1).2
      | .inr 2 => eqOneInner.2
      | .inr 3 => eqOneInner.2⟩⟩

/-- `eqOne` at its declared arity, as `combOf` and `isTreeOf`. -/
@[expose] def eqOneOf : COf 1 := ⟨eqOne, rfl⟩

/-- The one-test's meaning at its arity, taken at the raw tree rather than at
`eqOne`, as `combSem`. -/
@[expose] def eqOneSem : Sem 1 :=
  transport (fst_eval ⟨eqOneRaw, by decide⟩) (eval ⟨eqOneRaw, by decide⟩).2

/-- The one-test at an arbitrary environment is the test at the canonical
one. -/
theorem eqOneSem_env (f : Fin 1 → List Bool) : eqOneSem f = eqOneSem ![f 0] :=
  congrArg eqOneSem (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The one-test accepts exactly the bitstrings of length one. It is not a
recursion, so its three cases are decided by matching. -/
theorem eqOneSem_eq (u : List Bool) :
    eqOneSem ![u] = if u.length = 1 then [true] else [] := by
  match u with
  | [] => rfl
  | [b] => cases b <;> rfl
  | b :: c :: v =>
    cases b <;> cases c <;>
      (change ([] : List Bool) = _
       rw [if_neg (by simp only [List.length_cons]; omega)])

/-- The raw tree of the recognizer: the one-test on the scan's predecessor. -/
@[expose] def isTreeRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => eqOneRaw
    | .inr _ =>
      WType.mk (.comp 1 1) fun e ↦
        match e with
        | .inl () => predRaw
        | .inr _ => combRaw

/-- The recognizer: whether a bitstring is the preorder spelling of a binary
tree, as an expression of arity one. -/
@[expose] def isTree : C :=
  ⟨⟨isTreeRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => eqOne.2
      | .inr _ =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => comb.2⟩⟩⟩

/-- `isTree` at its declared arity. -/
@[expose] def isTreeOf : COf 1 := ⟨isTree, rfl⟩

/-- The recognizer's meaning at its arity, taken at the raw tree rather than
at `isTree`, as `combSem`. -/
@[expose] def isTreeSem : Sem 1 :=
  transport (fst_eval ⟨isTreeRaw, by decide⟩) (eval ⟨isTreeRaw, by decide⟩).2

/-- The meaning `isTreeSem` reads at the raw tree is the meaning `isTree`
carries, as `combSem_eq_eval` for the scan: the correctness statements below
are statements about the member of `C` that `isTree_smashFree` concerns. -/
theorem isTreeSem_eq_eval : transport isTreeOf.2 isTreeOf.1.eval = isTreeSem := rfl

/-- One step of the recognizer: the one-test on the scan's predecessor. The
scan's value is `[false]` on failure, whose predecessor is empty, and
otherwise the depth in unary offset by one, whose predecessor has length the
depth. -/
theorem isTreeSem_apply (w : List Bool) :
    isTreeSem ![w] = eqOneSem (fun _ ↦ (combSem ![w]).tail) := by
  change eqOneSem (fun _ ↦ predSem (fun _ ↦ combSem ![w])) = _
  generalize combSem ![w] = r
  congr 1
  funext _
  match r with
  | [] => rfl
  | b :: v => cases b <;> rfl

/-- The recognizer's value on both branches: a rejected word receives the
empty bitstring, not merely something other than `[true]`. -/
theorem isTreeSem_eq_ite (w : List Bool) :
    isTreeSem ![w] = if BinTree.Valid w then [true] else [] := by
  rw [isTreeSem_apply, eqOneSem_env, eqOneSem_eq, combSem_eq]
  by_cases h : BinTree.ok w = true
  · rw [if_pos h]
    simp only [List.tail_replicate, List.length_replicate, Nat.add_sub_cancel]
    by_cases hd : BinTree.depth w = 1
    · rw [if_pos hd, if_pos ⟨h, hd⟩]
    · rw [if_neg hd, if_neg fun hv : BinTree.Valid w ↦ hd hv.2]
  · rw [if_neg h, if_neg (by decide : ¬ ([false] : List Bool).tail.length = 1),
      if_neg fun hv : BinTree.Valid w ↦ h hv.1]

/-- The recognizer accepts exactly the words satisfying `BinTree.Valid`. -/
theorem isTreeSem_eq_singleton_iff_valid (w : List Bool) :
    isTreeSem ![w] = [true] ↔ BinTree.Valid w := by
  rw [isTreeSem_eq_ite]
  by_cases h : BinTree.Valid w
  · rw [if_pos h]
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · rw [if_neg h]
    exact ⟨fun hw ↦ absurd hw (by nofun), fun hv ↦ absurd hv h⟩

/-- The recognizer accepts exactly the preorder spellings of binary trees. -/
theorem isTreeSem_eq_singleton_iff_exists_print (w : List Bool) :
    isTreeSem ![w] = [true] ↔ ∃ t, BinTree.print t = w :=
  (isTreeSem_eq_singleton_iff_valid w).trans (BinTree.valid_iff_exists_print w)

/-- The recognizer lies in the smash-free subalgebra. With
[Strahm2003] Theorem 1(2)'s left-to-right inclusion, the decision of
`BinTree.Valid` is computable simultaneously in polynomial time and linear
space. -/
theorem isTree_smashFree : SmashFree isTree := by decide

end

end Cobham
