/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# Prototype: the morphisms the universe's type formers are functorial along

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

Example 3.6 of [GhaniNordvallForsbergMalatesta2015] shows that the
dependent-product former of a universe does not extend to an `IR⁺(Set)` or
`IR⁺(Setᵒᵖ)` code: interpreting the `δ` rule at a morphism `f : X' → X` of the
decoding category requires a map `Π X' (Y ∘ f) ⟶ Π X Y`, and there is none in
general. The paper's answer is to move to the groupoid `Set≅`, where every
morphism is invertible.

This module records that invertibility is more than the interpretation needs.
What it needs is a map backwards along `f`, and a section suffices:
`piMap` builds `Π X' (Y ∘ f) → Π X Y` from a chosen section of `f`, and
`piMap_id` and `piMap_comp` are its functor laws. The dependent-sum former needs
nothing (`sigmaMap`), and `not_piMap` is the counterexample, the same one the
paper gives and the one `Geb/Prototypes/FinCardUniverse/Value.lean` reproduces
in its finite model.

The resulting class of morphisms — split epimorphisms carrying a chosen section,
composing contravariantly in the sections — sits strictly between the
isomorphisms and all functions. `twIdEquivSplit` identifies it: a morphism
between identity arrows in the twisted-arrow category is exactly such a pair. So
the decoding category a Σ-and-Π universe can be interpreted over is at least the
diagonal of `Tw(C)`, not only the core groupoid.

## Main definitions

* `Split` — a function with a chosen section, with `Split.id` and `Split.comp`.
* `sigmaMap` — the dependent-sum former's action, along an arbitrary function.
* `piMap` — the dependent-product former's action, along a `Split`.
* `TwHom` — a morphism of the twisted-arrow category.

## Main statements

* `Split.id_comp`, `Split.comp_id`, `Split.comp_assoc` — `Split` composes as a
  category.
* `sigmaMap_id`, `sigmaMap_comp` — the dependent-sum former's functor laws.
* `piMap_id`, `piMap_comp` — the dependent-product former's functor laws, which
  is the claim: the interpretation is functorial along split epimorphisms, not
  merely along isomorphisms.
* `not_piMap` — no such map along an arbitrary function.
* `twIdEquivSplit` — `Split A B` is the hom-set of the twisted-arrow category
  between the identity arrows on `A` and on `B`.

## References

* [GhaniNordvallForsbergMalatesta2015]

## Tags

prototype, inductive-recursive, universe, variance, split epimorphism,
twisted arrow category
-/

@[expose] public section

universe u v

namespace GebProto.UniverseVariance

/-! ## Functions with a chosen section -/

/-- A function together with a chosen section: a split epimorphism whose section
is data rather than a property. The dependent-product former is functorial along
these; see `piMap`. -/
@[ext]
structure Split (A : Type u) (B : Type u) where
  /-- The function. -/
  toFun : A → B
  /-- The chosen section. -/
  sect : B → A
  /-- The section is a right inverse. -/
  toFun_sect : ∀ b, toFun (sect b) = b

namespace Split

/-- The identity, with the identity as its section. -/
def id (A : Type u) : Split A A where
  toFun := _root_.id
  sect := _root_.id
  toFun_sect _ := rfl

/-- Composition: the functions compose forwards and the sections backwards. -/
def comp {A B C : Type u} (e : Split A B) (e' : Split B C) : Split A C where
  toFun := e'.toFun ∘ e.toFun
  sect := e.sect ∘ e'.sect
  toFun_sect c := by
    change e'.toFun (e.toFun (e.sect (e'.sect c))) = c
    rw [e.toFun_sect, e'.toFun_sect]

/-- Composition with the identity on the left. -/
theorem id_comp {A B : Type u} (e : Split A B) : (Split.id A).comp e = e := rfl

/-- Composition with the identity on the right. -/
theorem comp_id {A B : Type u} (e : Split A B) : e.comp (Split.id B) = e := rfl

/-- Composition is associative. -/
theorem comp_assoc {A B C D : Type u} (e : Split A B) (e' : Split B C)
    (e'' : Split C D) : (e.comp e').comp e'' = e.comp (e'.comp e'') := rfl

/-- Every equivalence is split, so the groupoid of
[GhaniNordvallForsbergMalatesta2015]'s Example 3.6 is a special case: an
isomorphism is a function whose section happens to be a two-sided inverse. -/
def ofEquiv {A B : Type u} (e : A ≃ B) : Split A B where
  toFun := e
  sect := e.symm
  toFun_sect := e.apply_symm_apply

end Split

/-! ## The dependent-sum former

Its action needs no backward map: a reindexing of the bound object along any
function induces a map of dependent sums. -/

/-- The dependent-sum former's action along an arbitrary function. -/
def sigmaMap {X' X : Type u} (f : X' → X) (Y : X → Type v) :
    (Σ x' : X', Y (f x')) → Σ x : X, Y x :=
  fun p ↦ ⟨f p.1, p.2⟩

/-- The dependent-sum former's action along an identity is the identity. -/
theorem sigmaMap_id {X : Type u} (Y : X → Type v) :
    sigmaMap _root_.id Y = _root_.id :=
  rfl

/-- The dependent-sum former's action along a composite is the composite of the
actions. -/
theorem sigmaMap_comp {X'' X' X : Type u} (f : X'' → X') (f' : X' → X)
    (Y : X → Type v) :
    sigmaMap (f' ∘ f) Y = sigmaMap f' Y ∘ sigmaMap f (fun x' ↦ Y (f' x')) :=
  rfl

/-! ## The dependent-product former

Its action runs the reindexing backwards, which is what a chosen section
supplies. The transport along `toFun_sect` is the same move the discrete case
makes along an equality of decodings. -/

/-- The dependent-product former's action along a function with a chosen
section: evaluate the given section family at the chosen section, and transport
along the right-inverse witness. -/
def piMap {X' X : Type u} (e : Split X' X) (Y : X → Type v)
    (s : (x' : X') → Y (e.toFun x')) : (x : X) → Y x :=
  fun x ↦ cast (congrArg Y (e.toFun_sect x)) (s (e.sect x))

/-- The dependent-product former's action along the identity is the identity. -/
theorem piMap_id {X : Type u} (Y : X → Type v) :
    piMap (Split.id X) Y = _root_.id :=
  rfl

/-- The dependent-product former's action along a composite is the composite of
the actions: the interpretation is functorial on `Split`. -/
theorem piMap_comp {X'' X' X : Type u} (e : Split X'' X') (e' : Split X' X)
    (Y : X → Type v) :
    piMap (e.comp e') Y = piMap e' Y ∘ piMap e (fun x' ↦ Y (e'.toFun x')) := by
  funext s x
  exact (cast_cast _ _ _).symm

/-- Without a section there is no such map: the counterexample of Example 3.6 of
[GhaniNordvallForsbergMalatesta2015], with the empty object mapping to the
singleton and the family constant at the empty object. The empty product is
inhabited and the product of the constant family is not. -/
theorem not_piMap :
    ¬ Nonempty (∀ (X' X : Type) (f : X' → X) (Y : X → Type),
        ((x' : X') → Y (f x')) → ((x : X) → Y x)) :=
  fun ⟨h⟩ ↦ (h Empty Unit (fun e ↦ e.elim) (fun _ ↦ Empty) (fun e ↦ e.elim) ()).elim

/-! ## The twisted-arrow identification

`Tw(C)` has the morphisms of `C` as objects, and a morphism from `f : a ⟶ b` to
`g : c ⟶ d` is a pair `(src : c ⟶ a, tgt : b ⟶ d)` with `tgt ∘ f ∘ src = g`. Its
diagonal — the identity arrows — has exactly the `Split`s as its morphisms. -/

/-- A morphism of the twisted-arrow category of types: contravariant in the
source of the arrow, covariant in its target. -/
structure TwHom {a b c d : Type u} (f : a → b) (g : c → d) where
  /-- The action on the arrow's source, contravariant. -/
  src : c → a
  /-- The action on the arrow's target, covariant. -/
  tgt : b → d
  /-- The twisted commutation condition. -/
  comm : ∀ z, tgt (f (src z)) = g z

/-- A morphism between identity arrows in the twisted-arrow category is exactly
a function with a chosen section. Both round trips are definitional: the two
structures carry the same data under the relabelling `src ↦ sect`,
`tgt ↦ toFun`. -/
def twIdEquivSplit (A B : Type u) :
    TwHom (@_root_.id A) (@_root_.id B) ≃ Split A B where
  toFun t := ⟨t.tgt, t.src, t.comm⟩
  invFun e := ⟨e.sect, e.toFun, e.toFun_sect⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GebProto.UniverseVariance
