/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.UniverseVariance.Basic

/-!
# Prototype: the two type formers preserve retraction

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

`Geb/Prototypes/UniverseVariance/Basic.lean` gives the two type formers' action
along a `Split` in the bound object, with the binder's family fixed and read
through the reindexing. This module frees the family: the binder's family over
the source is an arbitrary family related to the one over the target by a
`Split` at each index, which is the shape a decoding takes once the codes have
moved as well.

The answer is that both formers preserve the relation, and functorially. No
coherence between the two levels is assumed: the data is a `Split` downstairs
and a `Split` at each index upstairs, and the section of the downstairs `Split`
is what supplies the reindexing the dependent-product former runs backwards.

Stated as a functor law, `sigmaSplit` and `piSplit` are the morphism maps of two
functors from the category whose objects are families `(X, Y)` and whose
morphisms `(X', Y') ⟶ (X, Y)` are a `Split X' X` together with a `Split` from
`Y' x'` to `Y` at the image of `x'`, to the category of types and `Split`s.

## Main definitions

* `sigmaSplit` — the dependent-sum former's action on such a pair.
* `piSplit` — the dependent-product former's action on such a pair.

## Main statements

* `sigmaSplit_id`, `sigmaSplit_comp` — the dependent-sum former's functor laws.
* `piSplit_id`, `piSplit_comp` — the dependent-product former's functor laws.
* `cast_apply` — a dependent function commutes with the transport along an
  equality of indices.
* `Split.toFun_cast`, `Split.sect_cast` — a family of `Split`s read at equal
  indices agrees with itself across the transport, which is what the composition
  laws need: the two sides apply the upstairs `Split` at indices that the
  downstairs section identifies only propositionally.

## References

* [GhaniNordvallForsbergMalatesta2015]

## Tags

prototype, inductive-recursive, universe, variance, split epimorphism, retract
-/

@[expose] public section

universe u v

namespace GebProto.UniverseVariance

/-- Transport along an equality of indices commutes with a dependent function. -/
theorem cast_apply {X : Type u} {Y : X → Type v} {a b : X} (hab : a = b) (h : Y a = Y b)
    (s : (x : X) → Y x) : cast h (s a) = s b := by
  cases hab; rfl

/-- A family of `Split`s over a reindexing, read at two indices identified by an
equality, agrees with itself across the transports on the sections. The
equalities of types are arbitrary arguments, so the lemma applies wherever the
transports arise. -/
theorem Split.sect_cast {X' X : Type u} {Y' : X' → Type v} {Y : X → Type v} {g : X' → X}
    (d : ∀ x', Split (Y' x') (Y (g x'))) {a b : X'} (hab : a = b) {x : X}
    (hb : Y x = Y (g b)) (ha : Y x = Y (g a)) (y : Y x) :
    (d b).sect (cast hb y) = cast (congrArg Y' hab) ((d a).sect (cast ha y)) := by
  cases hab; rfl

/-- A family of `Split`s over a reindexing, read at two indices identified by an
equality, agrees with itself across the transports on the functions. -/
theorem Split.toFun_cast {X' X : Type u} {Y' : X' → Type v} {Y : X → Type v} {g : X' → X}
    (d : ∀ x', Split (Y' x') (Y (g x'))) {a b : X'} (hab : b = a) {x : X}
    (hb : Y (g b) = Y x) (ha : Y (g a) = Y x) (hy : Y' b = Y' a) (z : Y' b) :
    cast hb ((d b).toFun z) = cast ha ((d a).toFun (cast hy z)) := by
  cases hab; rfl

/-! ## The dependent-sum former -/

/-- The dependent-sum former's action: the function pairs the images and the
section pairs the sections, the value transported along the right-inverse
witness of the `Split` on the bound object. -/
def sigmaSplit {X' X : Type u} {Y' : X' → Type v} {Y : X → Type v} (e : Split X' X)
    (d : ∀ x', Split (Y' x') (Y (e.toFun x'))) : Split (Σ x', Y' x') (Σ x, Y x) where
  toFun p := ⟨e.toFun p.1, (d p.1).toFun p.2⟩
  sect p := ⟨e.sect p.1, (d (e.sect p.1)).sect (cast (congrArg Y (e.toFun_sect p.1).symm) p.2)⟩
  toFun_sect p :=
    Sigma.ext (e.toFun_sect p.1) <|
      ((d (e.sect p.1)).toFun_sect _ ▸ cast_heq _ p.2 : _ ≍ p.2)

/-- The dependent-sum former's action along the identity is the identity. -/
theorem sigmaSplit_id {X : Type u} (Y : X → Type v) :
    sigmaSplit (Split.id X) (fun x ↦ Split.id (Y x)) = Split.id (Σ x, Y x) :=
  rfl

/-- The dependent-sum former's action on a composite is the composite of the
actions. -/
theorem sigmaSplit_comp {X'' X' X : Type u} {Y'' : X'' → Type v} {Y' : X' → Type v}
    {Y : X → Type v} (e : Split X'' X') (e' : Split X' X)
    (d' : ∀ x', Split (Y' x') (Y (e'.toFun x')))
    (d'' : ∀ x'', Split (Y'' x'') (Y' (e.toFun x''))) :
    sigmaSplit (e.comp e') (fun x'' ↦ (d'' x'').comp (d' (e.toFun x''))) =
      (sigmaSplit e d'').comp (sigmaSplit e' d') :=
  Split.ext rfl <| funext fun p ↦
    Sigma.ext rfl <| heq_of_eq <| congrArg _ <|
      Split.sect_cast d' (e.toFun_sect (e'.sect p.1)).symm _ _ p.2

/-! ## The dependent-product former -/

/-- The dependent-product former's action: the function evaluates at the section
on the bound object and transports along the right-inverse witness, and the
section evaluates at the function on the bound object. -/
def piSplit {X' X : Type u} {Y' : X' → Type v} {Y : X → Type v} (e : Split X' X)
    (d : ∀ x', Split (Y' x') (Y (e.toFun x'))) :
    Split ((x' : X') → Y' x') ((x : X) → Y x) where
  toFun t x := cast (congrArg Y (e.toFun_sect x)) ((d (e.sect x)).toFun (t (e.sect x)))
  sect s x' := (d x').sect (s (e.toFun x'))
  toFun_sect s := funext fun x ↦
    ((d (e.sect x)).toFun_sect _ ▸ cast_apply (e.toFun_sect x) _ s : _)

/-- The dependent-product former's action along the identity is the identity. -/
theorem piSplit_id {X : Type u} (Y : X → Type v) :
    piSplit (Split.id X) (fun x ↦ Split.id (Y x)) = Split.id ((x : X) → Y x) :=
  rfl

/-- The dependent-product former's action on a composite is the composite of the
actions: the reindexing along the section composes, so the interpretation is
functorial in the binder's family as well as in the bound object. -/
theorem piSplit_comp {X'' X' X : Type u} {Y'' : X'' → Type v} {Y' : X' → Type v}
    {Y : X → Type v} (e : Split X'' X') (e' : Split X' X)
    (d' : ∀ x', Split (Y' x') (Y (e'.toFun x')))
    (d'' : ∀ x'', Split (Y'' x'') (Y' (e.toFun x''))) :
    piSplit (e.comp e') (fun x'' ↦ (d'' x'').comp (d' (e.toFun x''))) =
      (piSplit e d'').comp (piSplit e' d') :=
  Split.ext (funext fun _t ↦ funext fun x ↦
    Split.toFun_cast d' (e.toFun_sect (e'.sect x)) _ _ _ _) rfl

end GebProto.UniverseVariance
