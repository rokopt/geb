/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FamBoundary
public import Geb.Prototypes.FinCardUniverse.Basic
public import Geb.Prototypes.PresheafIRProto.Basic

/-!
# Prototype: the universe functor's value as a family of codes

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

`Geb/Prototypes/FamBoundary.lean` shows that a presheaf of the form
`praPsh` — a sum over shapes of a representable times a set — lies in the image
of `Fam(C)`. This module records that the universe functor of
`FinCardUniverse.Basic` has a shape presheaf of exactly the form that lemma
needs, so its value is a family of codes.

`shapePshEquiv` is the identification: the shape type is the total space of the
family presheaf on `Code` with decoding `out former`. Its arities depend on a
shape only through that shape's code former, so at an input presheaf `Z` the
p.r.a. formula gives
`T(Z)(j) ≅ Σ_c (j ⟶ out c) × ArityHom c Z`, which is `praPsh` at
`S := Code`, `o := out former`, `A c := ArityHom c Z`.

So the coercion multiplicity that `Value` exhibits is no obstruction to reading
the value back as a family: it is absorbed into the code type, the free
coproduct completion being closed under set-indexed coproducts. What it does
obstruct is reading it back as an *inductive-recursive* family, and
`famDec_eq` is why: the decoding of a code is `out former c`, fixed by the
shape's declaration, with the arity hom — the codes the shape binds — nowhere in
it.

## Main definitions

* `universalShape` — the shape at a code former carrying the identity: the
  terminal object of that component of the shape presheaf's elements.
* `famCode` / `famDec` — the codes and decoding of the family the value
  presents: a code former together with an arity hom, decoding by the former
  alone.

## Main statements

* `shapePshEquiv` / `arityPshEquiv` — the shape type and each arity are total
  spaces of family presheaves, so both are coproducts of slices.
* `famDec_eq` — the decoding does not mention the arity hom.

## References

* [GhaniNordvallForsbergMalatesta2015]

## Tags

prototype, presheaf, free coproduct completion, universe, inductive-recursive
-/

@[expose] public section

open CategoryTheory GebProto.FamBoundary

namespace GebProto.FinCardUniverse

/-- The shape type is the total space of the family presheaf on `Code` with
decoding `out former`: a shape is a code former together with an object and a
morphism into what that former's output decodes to. This is the hypothesis
`FamBoundary.isFamPsh_praPsh` needs of a shape presheaf. -/
def shapePshEquiv (former : Former) :
    Shp former ≃ Σ j : Card, (famPsh Code (out former)).obj ⟨j⟩ where
  toFun a := ⟨a.2.1, a.1, a.2.2⟩
  invFun p := ⟨p.2.1, p.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The arity of a shape is also the total space of a family presheaf: on the
representable summands, with decoding `bound`. So both halves of the functor's data
are coproducts of representables — coproducts of slices, in the element picture
— and strictness still fails. The coercion does not come from the shape or the
arity being general presheaves; it comes from mapping *into* the input, where
`Z(i) = Σ_u (i ⟶ d u)` replaces the fibre `{u | d u = i}`. -/
def arityPshEquiv (former : Former) (a : Shp former) :
    Dir a ≃ Σ i : Card, (famPsh (Idx a.1) (bound a.1)).obj ⟨i⟩ where
  toFun b := ⟨b.2.1, b.1, b.2.2⟩
  invFun p := ⟨p.2.1, p.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The universal shape at a code former: the one over the object its output
decodes to, carrying the identity. It is the terminal object of that component
of the shape presheaf's category of elements, which is what makes the shape
presheaf a family presheaf. -/
def universalShape (former : Former) (c : Code) : Shp former :=
  ⟨c, out former c, 𝟙 _⟩

/-- The codes of the family the universe functor's value presents: a code former
together with an arity hom at its universal shape — the codes it binds, and the
coercions witnessing that they fit. -/
def famCode (former : Former) (Z : Cardᵒᵖ ⥤ Type) : Type :=
  Σ c : Code, ArityHom (universeFunctor former) (universalShape former c) Z

/-- The decoding of such a code: the object the code former's output decodes to,
read off the shape alone. -/
def famDec (former : Former) (Z : Cardᵒᵖ ⥤ Type) : famCode former Z → Card :=
  fun p ↦ out former p.1

/-- The decoding does not mention the arity hom: two codes with the same code
former decode alike however differently they bind. This is what separates the
value from an inductive-recursive family, whose binder codes decode by the
decodings of the codes they bind. -/
theorem famDec_eq (former : Former) (Z : Cardᵒᵖ ⥤ Type) (c : Code)
    (x y : ArityHom (universeFunctor former) (universalShape former c) Z) :
    famDec former Z ⟨c, x⟩ = famDec former Z ⟨c, y⟩ :=
  rfl

end GebProto.FinCardUniverse
