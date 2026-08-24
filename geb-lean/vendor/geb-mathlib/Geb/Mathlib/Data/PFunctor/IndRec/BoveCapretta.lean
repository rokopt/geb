/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Indexed
public import Mathlib.Data.Fin.VecNotation

/-!
# The Bove-Capretta domain of a call-by-value evaluator

Example 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: the
Bove-Capretta method [BoveCapretta2001], which presents the domain of a
partial function as an inductive family, applied to the call-by-value
evaluator of the untyped lambda calculus

    cbv (var x)   = var x
    cbv (lam t)   = lam t
    cbv (app f s) with cbv f
      | lam t = cbv (subst0 (cbv s) t)
      | f'    = app f' (cbv s)

which is not structurally recursive: in the application case the third
recursive call is made at a term built from the results of the first two.
The domain therefore has to be defined simultaneously with the
evaluation, which is a job for indexed induction-recursion. Both indices
are `Tm` and both decodings are the constant family at `Tm`: the index is
the term being evaluated and the decoded value is the term it evaluates
to. `BoveCapretta.Dom t` is the evidence that the evaluator terminates on
`t`, and `BoveCapretta.eval` reads the resulting value off that evidence.

## Main definitions

* `BoveCapretta.TmShape`, `BoveCapretta.tmDirection`,
  `BoveCapretta.tmPFunctor`, `BoveCapretta.Tm` — the untyped lambda terms
  in de Bruijn form, as the W-type of a polynomial functor, with
  constructors `BoveCapretta.tmVar`, `BoveCapretta.tmApp` and
  `BoveCapretta.tmLam`.
* `BoveCapretta.tmShift`, `BoveCapretta.tmSubst`,
  `BoveCapretta.subst0` — raising the free variables at or above a
  cutoff, substitution for a named variable, and substitution for
  variable `0`.
* `BoveCapretta.Code`, `BoveCapretta.stop`, `BoveCapretta.call` — the
  `IIR` codes of the domain and the two code forms it is built from, a
  delivered input-output pair and a recursive call.
* `BoveCapretta.appBranch`, `BoveCapretta.branch`, `BoveCapretta.code`,
  `BoveCapretta.irCode` — the application case's branch once the function
  part's value is known, the branch at each term, the domain code, and
  the plain `IR` code it reduces to.
* `BoveCapretta.Dom`, `BoveCapretta.eval` — the domain predicate and the
  evaluator reading a value off a domain element.
* `BoveCapretta.lamMu`, `BoveCapretta.varMu`,
  `BoveCapretta.lamEvidence`, `BoveCapretta.varEvidence` — the domain
  elements of the values, which need no recursive evidence.
* `BoveCapretta.identity`, `BoveCapretta.identityApp`,
  `BoveCapretta.identityAppEvidence` — the identity, its
  self-application, and the evidence that the evaluator terminates on the
  latter.

## Main statements

* `BoveCapretta.eval_lamEvidence`, `BoveCapretta.eval_varEvidence` — a
  value evaluates to itself.
* `BoveCapretta.eval_identityApp` — the self-application of the identity
  evaluates to the identity.

## Implementation notes

The application case makes essential use of the delivered values: the
code taken after the first recursive field is chosen by that field's
decoded value, and the third recursive field's index is built from the
second's. This is what `IIR.delta1` is for, and what an inductive family
without the simultaneous decoding could not express.

The domain elements are built by `IR.W.mk` at the reduced code
`IIR.toIR`, where the index constraints the reduction introduces
(`IR.sigma` over a pointwise equality) appear as data: the `PLift.up`
beside each recursive field is the proof that the field decoded to the
index the indexed code demanded. In the indexed presentation those proofs
are implicit in the family's index.

Every equation here holds by reduction: the code is closed, so the fold
`IR.posSlice` that `IR.W.mk` and `IR.wDecode` are built from computes.

## References

* [BoveCapretta2001]
* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

indexed induction-recursion, Bove-Capretta, general recursion, partial
function, lambda calculus, call-by-value
-/

@[expose] public section

namespace IndRec

namespace BoveCapretta

/-- The three node forms of the untyped lambda terms: a de Bruijn
variable, an application, and an abstraction. -/
inductive TmShape
  | var (n : ℕ)
  | app
  | lam

/-- The subterm positions of a term shape: a variable has none, an
application has its function and argument parts, an abstraction its
body. -/
@[reducible] def tmDirection : TmShape → Type
  | .var _ => Fin 0
  | .app => Fin 2
  | .lam => Fin 1

/-- The signature of the untyped lambda terms as a polynomial
functor. -/
@[reducible] def tmPFunctor : PFunctor.{0, 0} := ⟨TmShape, tmDirection⟩

/-- The untyped lambda terms in de Bruijn form. -/
def Tm : Type := PFunctor.W tmPFunctor

/-- The de Bruijn variable `n`. -/
def tmVar (n : ℕ) : Tm := WType.mk (.var n) Fin.elim0

/-- The application of `f` to `a`. -/
def tmApp (f a : Tm) : Tm := WType.mk .app ![f, a]

/-- The abstraction with body `t`. -/
def tmLam (t : Tm) : Tm := WType.mk .lam ![t]

/-- The algebra raising the free variables at or above a cutoff by one:
the cutoff crosses a binder incremented. -/
def tmShiftStep : tmPFunctor.Obj (ℕ → Tm) → (ℕ → Tm) :=
  fun ⟨shape, v⟩ ↦ match shape, v with
  | .var k, _ => fun c ↦ tmVar (if k < c then k else k + 1)
  | .app, v => fun c ↦ tmApp (v 0 c) (v 1 c)
  | .lam, v => fun c ↦ tmLam (v 0 (c + 1))

/-- Raise by one the free variables of `t` at or above the cutoff `c`. -/
def tmShift (c : ℕ) (t : Tm) : Tm := WType.elim (ℕ → Tm) tmShiftStep t c

/-- The algebra substituting a term for a named variable, decrementing
the free variables above it since the binder is being removed. Crossing a
binder increments the variable and shifts the substituted term. -/
def tmSubstStep : tmPFunctor.Obj (ℕ → Tm → Tm) → (ℕ → Tm → Tm) :=
  fun ⟨shape, v⟩ ↦ match shape, v with
  | .var k, _ =>
      fun n s ↦ if k < n then tmVar k else if k = n then s else tmVar (k - 1)
  | .app, v => fun n s ↦ tmApp (v 0 n s) (v 1 n s)
  | .lam, v => fun n s ↦ tmLam (v 0 (n + 1) (tmShift 0 s))

/-- Substitute `s` for the variable `n` in `t`. -/
def tmSubst (n : ℕ) (s t : Tm) : Tm :=
  WType.elim (ℕ → Tm → Tm) tmSubstStep t n s

/-- Substitute `s` for the variable `0` in `t`: the term a beta-redex
`app (lam t) s` contracts to. -/
def subst0 (s t : Tm) : Tm := tmSubst 0 s t

/-- The `IIR` codes of the domain: both indices are `Tm` and both
decodings the constant family at `Tm`, the index being the term evaluated
and the decoding the term it evaluates to. -/
def Code : Type 1 := IIR.{0, 0, 0, 0, 0, 0} Tm (fun _ ↦ Tm) Tm (fun _ ↦ Tm)

/-- The constant code delivering the input-output pair `(m, ev)`. -/
def stop (m ev : Tm) : Code := IIR.iota Tm (fun _ ↦ Tm) Tm (fun _ ↦ Tm) m ev

/-- A single recursive call at `n`, whose decoded value the continuation
receives. -/
def call (n : Tm) (c : Tm → Code) : Code :=
  IIR.delta1 Tm (fun _ ↦ Tm) Tm (fun _ ↦ Tm) n c

/-- The branch of the application node `t`, with argument `a`, taken once
its function part's value `fv` is known. When that value is an
abstraction the evaluator recurses on the substituted body, at an index
built from the argument's value; otherwise it stops at the application of
the two values. -/
def appBranch (t a fv : Tm) : Code :=
  match fv with
  | ⟨.lam, w⟩ =>
      call a fun av ↦ call (subst0 av (w 0)) fun bv ↦ stop t bv
  | _ => call a fun av ↦ stop t (tmApp fv av)

/-- The branch of the domain code at each term: a value is delivered
immediately, and an application first evaluates its function part, the
delivered value choosing how to carry on. -/
def branch (t : Tm) : Code :=
  match t with
  | ⟨.var _, _⟩ => stop t t
  | ⟨.lam, _⟩ => stop t t
  | ⟨.app, v⟩ => call (v 0) (appBranch t (v 1))

/-- The domain code: a choice of the term being evaluated, then that
term's branch. -/
def code : Code := IIR.sigma Tm (fun _ ↦ Tm) Tm (fun _ ↦ Tm) Tm branch

/-- The plain `IR` code the domain code reduces to, over the total space
of the constant family at `Tm`. -/
def irCode : IR.{0, 0, 0, 0} (Σ _ : Tm, Tm) (Σ _ : Tm, Tm) :=
  IIR.toIR Tm (fun _ ↦ Tm) Tm (fun _ ↦ Tm) code

/-- The evidence that the evaluator terminates on a term. -/
def Dom : Tm → Type := IIR.W.{0, 0, 0, 0} Tm (fun _ ↦ Tm) code

/-- The value the evaluator returns, read off the termination
evidence. -/
def eval : (t : Tm) → Dom t → Tm :=
  IIR.wDecode Tm (fun _ ↦ Tm) code

/-- The element of the reduced code's data type for an abstraction: a
value reaches a constant code immediately, so its node carries no
recursive field. -/
def lamMu (t : Tm) : IR.W.{0, 0, 0} (Σ _ : Tm, Tm) irCode :=
  IR.W.mk (Σ _ : Tm, Tm) irCode ⟨tmLam t, ULift.up ()⟩

/-- The element of the reduced code's data type for a variable. -/
def varMu (n : ℕ) : IR.W.{0, 0, 0} (Σ _ : Tm, Tm) irCode :=
  IR.W.mk (Σ _ : Tm, Tm) irCode ⟨tmVar n, ULift.up ()⟩

/-- The evaluator terminates on an abstraction. -/
def lamEvidence (t : Tm) : Dom (tmLam t) := ⟨lamMu t, rfl⟩

/-- The evaluator terminates on a variable. -/
def varEvidence (n : ℕ) : Dom (tmVar n) := ⟨varMu n, rfl⟩

/-- An abstraction evaluates to itself. -/
theorem eval_lamEvidence (t : Tm) : eval (tmLam t) (lamEvidence t) = tmLam t := rfl

/-- A variable evaluates to itself. -/
theorem eval_varEvidence (n : ℕ) : eval (tmVar n) (varEvidence n) = tmVar n := rfl

/-- The identity term. -/
def identity : Tm := tmLam (tmVar 0)

/-- The self-application of the identity. -/
def identityApp : Tm := tmApp identity identity

/-- The evidence that the evaluator terminates on the self-application of
the identity: one recursive field for the function part, one for the
argument, and one for the substituted body, which here is the identity
again. Beside each field is the proof that it decoded to the index the
indexed code demanded, which the reduction to `IR` turns from an index
into data. -/
def identityAppEvidence : Dom identityApp :=
  ⟨IR.W.mk (Σ _ : Tm, Tm) irCode
      ⟨identityApp,
        fun _ ↦ lamMu (tmVar 0), ULift.up (PLift.up fun _ ↦ rfl),
        fun _ ↦ lamMu (tmVar 0), ULift.up (PLift.up fun _ ↦ rfl),
        fun _ ↦ lamMu (tmVar 0), ULift.up (PLift.up fun _ ↦ rfl),
        ULift.up ()⟩,
    rfl⟩

/-- The self-application of the identity evaluates to the identity. -/
theorem eval_identityApp : eval identityApp identityAppEvidence = identity := rfl

end BoveCapretta

end IndRec
