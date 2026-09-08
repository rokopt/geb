/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Batteries.Tactic.Lint

/-!
# Prototype: where strong dinaturality and parametricity part

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

A transformation between mixed-variant difunctors is paranatural when it
preserves the morphisms of the category of diagonal elements
([Neumann2023] Definition 2.7), which is strong dinaturality. Whether that
condition is parametricity depends on the difunctor structure carried at a
negative occurrence, and the two part at
`∀ X, ((X → X) → X) → X`: [Neumann2023] Section 6.2 names it as the simplest
type on which the strong-dinaturality condition read off the twisted
exponential is not the free theorem, and retracts the claim that the two
coincide.

This module reproduces that separation at the smallest scale that hosts it,
`Unit` and `Bool`. Both conditions say when `j : I → J` carries `p` to `q`:
`ParanaturalHom` is the free theorem's hypothesis, relating `p` and `q` at any
pair of endomorphisms `j` intertwines; `TwistedHom` is the hypothesis the
twisted exponential produces, which reaches only the endomorphism pairs cut out
by a function `J → I`. `twistedHom_of_paranaturalHom` is one containment and
`not_paranaturalHom_unitBool` refutes the other, so strong dinaturality over the
twisted exponential is the *stronger* condition on a transformation: it demands
the conclusion in cases the free theorem exempts.

`selfApply` is what it excludes. It is the System F term
`Λ X. λ p. p (λ x. x)`, so it satisfies its type's free theorem
(`selfApply_paranatural`, which holds at every instance), and
`not_selfApply_twisted` shows it is not strongly dinatural over the twisted
exponential.

The rank the separation sits at is the one a universe closed under dependent
products reaches when a dependent-product code is applied to a dependent-product
code: the domain of the outer former is then the value of another former, so the
bound object occurs negatively inside a negative position, which is the nesting
`((X → X) → X) → X` has and `(X → X) → X` does not. What the separation costs is
therefore the difunctor structure and not paranaturality itself: [Neumann2023]
Section 6.2 records that the paranatural exponential gives this type the
free theorem's condition, which is `ParanaturalHom` here.

## Main definitions

* `ParanaturalHom` — the free theorem's hypothesis at `∀ X, ((X → X) → X) → X`,
  which is the morphism condition of the paranatural exponential.
* `TwistedHom` — the strong-dinaturality hypothesis the twisted exponential
  gives the same type.
* `selfApply` — the System F term `Λ X. λ p. p (λ x. x)`.

## Main statements

* `twistedHom_of_paranaturalHom` — every paranatural morphism is a twisted one.
* `twistedHom_unitBool`, `not_paranaturalHom_unitBool` — the converse fails, at
  `Unit` and `Bool`.
* `selfApply_paranatural` — `selfApply` satisfies the free theorem everywhere.
* `not_selfApply_twisted` — and is not strongly dinatural over the twisted
  exponential, so the stronger condition excludes a term of the type.

## Implementation notes

Both hypotheses are transcribed from [Neumann2023] Section 6.2 as that section
states them. Neither is derived here from a formalization of the two
exponentials, so what the module establishes is that the two conditions differ,
not that they are the conditions those two difunctor structures produce.

## References

* [Neumann2023]

## Tags

prototype, paranatural, strong dinaturality, parametricity, free theorem,
difunctor
-/

@[expose] public section

namespace GebProto.ParanaturalRank

/-! ## The two hypotheses

Both say when `j : I → J` carries `p` to `q`, for `p` and `q` the components at
`I` and at `J` of the difunctor `((- → -) → -)`. They differ in which pairs of
endomorphisms they range over. -/

/-- The free theorem's hypothesis at `∀ X, ((X → X) → X) → X`: `j` relates `p`
to `q` at every pair of endomorphisms it intertwines. This is the morphism
condition of [Neumann2023]'s paranatural exponential. -/
def ParanaturalHom {I J : Type} (j : I → J) (p : (I → I) → I) (q : (J → J) → J) : Prop :=
  ∀ (x : I → I) (y : J → J), j ∘ x = y ∘ j → j (p x) = q y

/-- The strong-dinaturality hypothesis the twisted exponential gives the same
type: `j` relates `p` to `q` at the endomorphism pairs `(r ∘ j, j ∘ r)` cut out
by a function `r : J → I`. The dependence on a function backwards is what
[Neumann2023] Section 6.2 identifies as the departure. -/
def TwistedHom {I J : Type} (j : I → J) (p : (I → I) → I) (q : (J → J) → J) : Prop :=
  ∀ r : J → I, j (p (r ∘ j)) = q (j ∘ r)

/-- Every endomorphism pair the twisted hypothesis reaches is one `j`
intertwines, so the free theorem's hypothesis is the stronger of the two and the
condition it imposes on a transformation the weaker. -/
theorem twistedHom_of_paranaturalHom {I J : Type} {j : I → J} {p : (I → I) → I}
    {q : (J → J) → J} (h : ParanaturalHom j p q) : TwistedHom j p q :=
  fun r ↦ h (r ∘ j) (j ∘ r) rfl

/-! ## The separating instance

`Unit` and `Bool`. The only function `Bool → Unit` is the constant one, so the
twisted hypothesis has a single instance and it holds; the identity pair, which
`j` intertwines, is outside its range and refutes the other. -/

/-- The map picking out `true`. -/
@[nolint unusedArguments] def jUnitBool : Unit → Bool :=
  fun _ ↦ true

/-- The only element of `(Unit → Unit) → Unit`. -/
@[nolint unusedArguments] def pUnit : (Unit → Unit) → Unit :=
  fun _ ↦ ()

/-- Evaluation at `false`, which separates the identity from the constant map at
`true`. -/
def qBool : (Bool → Bool) → Bool :=
  fun y ↦ y false

/-- The twisted hypothesis holds: its one instance evaluates a constant map. -/
theorem twistedHom_unitBool : TwistedHom jUnitBool pUnit qBool :=
  fun _ ↦ rfl

/-- The free theorem's hypothesis fails, at the identity pair. -/
theorem not_paranaturalHom_unitBool : ¬ ParanaturalHom jUnitBool pUnit qBool :=
  fun h ↦ Bool.noConfusion (h _root_.id _root_.id rfl)

/-! ## The term the twisted condition excludes -/

/-- The System F term `Λ X. λ p. p (λ x. x)`, an inhabitant of
`∀ X, ((X → X) → X) → X`. -/
def selfApply (X : Type) (p : (X → X) → X) : X :=
  p _root_.id

/-- `selfApply` satisfies its type's free theorem, at every instance: the
hypothesis at the identity pair is the conclusion. -/
theorem selfApply_paranatural {I J : Type} (j : I → J) (p : (I → I) → I)
    (q : (J → J) → J) (h : ParanaturalHom j p q) : j (selfApply I p) = selfApply J q :=
  h _root_.id _root_.id rfl

/-- `selfApply` is not strongly dinatural over the twisted exponential. So the
two conditions are not the same condition, and the one the twisted exponential
imposes rejects a term of the type. -/
theorem not_selfApply_twisted :
    ¬ ∀ (I J : Type) (j : I → J) (p : (I → I) → I) (q : (J → J) → J),
        TwistedHom j p q → j (selfApply I p) = selfApply J q :=
  fun h ↦ Bool.noConfusion
    (h Unit Bool jUnitBool pUnit qBool twistedHom_unitBool)

end GebProto.ParanaturalRank
