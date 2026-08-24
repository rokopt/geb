/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.W
public import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# A language of sums and products

Example 2 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: numerical
expressions closed under constants, finite sums and finite products, each
expression decoding to its value. The expressions and the decoding are
defined together because the decoding is what determines the domains: a
sum ranges over `Fin` of the value of its bound, so the type of a node's
later fields depends on the values of its earlier ones. That is an
inductive-recursive definition, and it is presented here as an endo-code
`Language.code : IR ℕ ℕ`, whose data type and decoder are
`Language.Expr` and `Language.value`.

## Main definitions

* `Language.Tag`, `Language.tagCode` — the three node forms and the code
  of each.
* `Language.code` — the code of the language, the `lang` of Example 2.
* `Language.Expr`, `Language.value` — the expressions and their values.
* `Language.lit`, `Language.sum`, `Language.prod` — the three expression
  constructors. The summand family of `Language.sum` is indexed by `Fin`
  of the *value* of the bound, not by the bound.
* `Language.sumFirstFive` — the paper's example expression, $\sum_{n<5} n$.

## Main statements

* `Language.value_lit`, `Language.value_sum`, `Language.value_prod` — the
  value of each expression form.
* `Language.value_sumFirstFive` — the paper's example decodes to `10`.

## Implementation notes

The finitary summation and product the example calls for are `List.sum`
and `List.prod` of `List.ofFn`, so the `sum` and `prod` of Example 2 need
no definition of their own. Taking them over `Finset.univ` instead would
work equally well but is not `Classical.choice`-free: the `Fintype (Fin
n)` instance behind `Finset.univ` depends on it.

Every value equation holds by reduction: the code is closed, so the fold
`IR.posSlice` that `IR.W.mk` and `IR.wDecode` are built from computes.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, initial algebra, sum, product
-/

@[expose] public section

open CategoryTheory

namespace IndRec

namespace Language

/-- The three node forms of the language: a literal, a finite sum, and a
finite product. -/
inductive Tag
  | lit
  | sum
  | prod

/-- The code of each node form. A literal node carries a natural number
and decodes to it. A sum node carries one recursive field, its bound, and
then a family of recursive fields indexed by `Fin` of the bound's decoded
value; it decodes to the sum of that family's values. A product node is
the same with the product. -/
def tagCode : Tag → IR.{0, 0, 0, 0} ℕ ℕ
  | .lit => IR.sigma ℕ ℕ ℕ fun n ↦ IR.iota ℕ ℕ n
  | .sum =>
      IR.delta ℕ ℕ PUnit fun n ↦
        IR.delta ℕ ℕ (Fin (n PUnit.unit)) fun f ↦ IR.iota ℕ ℕ (List.ofFn f).sum
  | .prod =>
      IR.delta ℕ ℕ PUnit fun n ↦
        IR.delta ℕ ℕ (Fin (n PUnit.unit)) fun f ↦ IR.iota ℕ ℕ (List.ofFn f).prod

/-- The code of the language: a choice of node form, then that form's
code. -/
def code : IR.{0, 0, 0, 0} ℕ ℕ := IR.sigma ℕ ℕ Tag tagCode

/-- The expressions of the language: the data type `Language.code`
describes. -/
def Expr : Type := IR.W.{0, 0, 0} ℕ code

/-- The value of an expression: the decoder `Language.code` describes. -/
def value : Expr → ℕ := IR.wDecode ℕ code

/-- The literal expression carrying `n`. -/
def lit (n : ℕ) : Expr := IR.W.mk ℕ code ⟨.lit, n, ULift.up ()⟩

/-- The finite sum of the family `f`, over `Fin` of the value of the
bound `b`. -/
def sum (b : Expr) (f : Fin (value b) → Expr) : Expr :=
  IR.W.mk ℕ code ⟨.sum, fun _ ↦ b, f, ULift.up ()⟩

/-- The finite product of the family `f`, over `Fin` of the value of the
bound `b`. -/
def prod (b : Expr) (f : Fin (value b) → Expr) : Expr :=
  IR.W.mk ℕ code ⟨.prod, fun _ ↦ b, f, ULift.up ()⟩

/-- A literal decodes to the natural number it carries. -/
@[simp]
theorem value_lit (n : ℕ) : value (lit n) = n := rfl

/-- A sum decodes to the sum of its summands' values. -/
@[simp]
theorem value_sum (b : Expr) (f : Fin (value b) → Expr) :
    value (sum b f) = (List.ofFn fun i ↦ value (f i)).sum := rfl

/-- A product decodes to the product of its factors' values. -/
@[simp]
theorem value_prod (b : Expr) (f : Fin (value b) → Expr) :
    value (prod b f) = (List.ofFn fun i ↦ value (f i)).prod := rfl

/-- The example expression of Example 2 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]: $\sum_{n<5} n$, whose
summand family coerces its `Fin`-valued index to a literal. -/
def sumFirstFive : Expr := sum (lit 5) fun n ↦ lit n.val

/-- The example expression decodes to `10`. -/
theorem value_sumFirstFive : value sumFirstFive = 10 := rfl

end Language

end IndRec
