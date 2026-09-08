/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LargeIR.Morphism
public import Geb.Mathlib.CategoryTheory.Grothendieck.Basic
public import Mathlib.CategoryTheory.Pi.Basic

set_option doc.verso true

/-!
# Prototype: the free coproduct completion as a Grothendieck construction

Throwaway exploration, not upstream-eligible content. This module names
mathlib's {name}`CategoryTheory.Cat` and functor categories, so it depends on
{name}`Classical.choice` and is listed in {lit}`GebMeta.classicalAllowedModules`;
its content is packaging, the choice-free content being in
{name}`GebProto.LargeIR.FamHom` and {name}`GebProto.LargeIR.codeMap`.

The free coproduct completion {lit}`Fam(Type)`, with its morphisms proper,
is the contravariant Grothendieck construction {name}`CategoryTheory.CoGrothendieck`
of the functor {lit}`famFib : Typeᵒᵖ ⥤ Cat` sending an index type {lit}`U`
to the category {lit}`U → Type` of families over it, with pointwise
morphisms, and a map of index types to precomposition,
{name}`CategoryTheory.Pi.comap`, which is strictly functorial. Its objects
are the objects of {name}`CategoryTheory.FreeCoprodCompDisc` at {lit}`Type`,
{lit}`objGrEquiv`, and its morphisms are {name}`GebProto.LargeIR.FamHom`,
{lit}`homGrEquiv`: a base map with a fibre morphism into the precomposed
family. The action {name}`GebProto.LargeIR.codeMap` of the code
{name}`GebProto.LargeIR.code` on morphisms of families then packages, with
its laws {name}`GebProto.LargeIR.codeMap_id` and
{name}`GebProto.LargeIR.codeMap_comp`, as an endofunctor {lit}`codeFunctor`
of the construction: the interpretation of the code as a functor on
{lit}`Fam(Type)` proper, which is the positive inductive-recursive
interpretation of \[GhaniNordvallForsbergMalatesta2015\] for this code.

## Main definitions

* {lit}`famFib` — the functor {lit}`Typeᵒᵖ ⥤ Cat`, {lit}`U ↦ (U → Type)`.
* {lit}`FamGr` — {lit}`Fam(Type)` as its contravariant Grothendieck
  construction.
* {lit}`objGrEquiv`, {lit}`homGrEquiv` — its objects are the families and
  its morphisms are {name}`GebProto.LargeIR.FamHom`.
* {lit}`codeFunctor` — the code's interpretation as an endofunctor of
  {lit}`FamGr`.

## References

* \[GhaniNordvallForsbergMalatesta2015\]

## Tags

prototype, free coproduct completion, Grothendieck construction,
inductive-recursive, code
-/

@[expose] public section

open CategoryTheory IndRec

namespace GebProto.LargeIR

/-! # The Grothendieck construction -/

/-- The functor {lit}`Typeᵒᵖ ⥤ Cat` sending an index type to the category of
families over it and a map of index types to precomposition. -/
def famFib : Typeᵒᵖ ⥤ Cat.{0, 1} where
  obj U := Cat.of (U.unop → Type)
  map h := (Pi.comap (fun _ ↦ Type) h.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- {lit}`Fam(Type)` as the contravariant Grothendieck construction of
{lit}`famFib`. -/
abbrev FamGr : Type 1 :=
  CoGrothendieck famFib

/-- A family as an object of the construction. -/
def toGr (F : FreeCoprodCompDisc.{0, 1} Type) : FamGr :=
  CoGrothendieck.mk F.1 F.2

/-- An object of the construction as a family. -/
def ofGr (A : FamGr) : FreeCoprodCompDisc.{0, 1} Type :=
  ⟨A.base, A.fiber⟩

/-- The objects of the construction are the families. -/
def objGrEquiv : FreeCoprodCompDisc.{0, 1} Type ≃ FamGr where
  toFun := toGr
  invFun := ofGr
  left_inv _ := rfl
  right_inv _ := rfl

/-- The morphisms of the construction are the morphisms of families: a base
map with a fibre morphism into the precomposed family. -/
def homGrEquiv (F G : FreeCoprodCompDisc.{0, 1} Type) : FamHom F G ≃ (toGr F ⟶ toGr G) where
  toFun φ := CoGrothendieck.homMk (↾ φ.1) fun u ↦ ↾ φ.2 u
  invFun f := ⟨CoGrothendieck.homBase f, fun u ↦ CoGrothendieck.homFiber f u⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! # The code as an endofunctor -/

variable {X Y : Type} (P : SlicePFunctor.{0, 0, 0, 0} X Y)

/-- The interpretation of the code as an endofunctor of {lit}`Fam(Type)`:
{name}`IndRec.IR.interpObj` on objects and {name}`GebProto.LargeIR.codeMap`
on morphisms. -/
def codeFunctor : FamGr ⥤ FamGr where
  obj A := toGr (IR.interpObj Type Type (code P) (ofGr A))
  map f := homGrEquiv _ _ (codeMap P ((homGrEquiv _ _).symm f))
  map_id _ := rfl
  map_comp _ _ := rfl

end GebProto.LargeIR
