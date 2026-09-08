/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.UniverseVariance.Retract

/-!
# Prototype: the two universe examples over the split-epimorphism base

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

Examples 3.5 and 3.6 of [GhaniNordvallForsbergMalatesta2015] over a decoding
category whose morphisms carry a chosen section. The paper's Example 3.5 gives
the dependent-sum universe over `Fam(Setᵒᵖ)` and its Example 3.6 shows the
dependent-product universe extends to neither `Fam(Set)` nor `Fam(Setᵒᵖ)`, only
to the groupoid `Fam(Set≅)`. Here both are given over `Fam` of the category
whose morphisms are embedding-projection pairs: the morphism map that Example
3.6 shows cannot exist over `Set` is `piUnivHom`.

`FamHom`'s components are an embedding-projection pair, the form the section
takes once the decoding maps are packaged: a map each way with `proj ∘ emb` the
identity. That is the classical device for solving recursive domain equations —
restricting to the subcategory of embeddings makes a mixed-variance functor
covariant, as in Theorem 5.8 of [LindenhoviusMisloveZamdzhiev2021] — transported
to the inductive-recursive setting.

The code map `univCodeMap` reindexes the binder's family along `proj`. That is
the `replace` of the discrete presentation. The decoding component at a binder
code is the corresponding former's action on the pair of the `Split` at the
bound code and the `Split` at each code the binder binds, so both morphism maps
are `Geb/Prototypes/UniverseVariance/Retract.lean` applied to `FamHom`'s data,
and their functor laws are that module's.

## Main definitions

* `Fam` / `FamHom` — a family of types, and a map of codes together with a
  `Split` at each code: the projection is the split epimorphism and the
  embedding its chosen section.
* `FamHom.proj` / `FamHom.emb` / `FamHom.proj_emb` — the pair read off.
* `FamHom.id` / `FamHom.comp` — the identity and composition.
* `UnivCode` / `univDec` / `univObj` — the universe functor on objects,
  parameterized by a base type and a type former.
* `univCodeMap` — its action on codes, reindexing the binder's family along
  `proj`.
* `sigmaFormer` / `piFormer` — the two formers.
* `sigmaUnivHom` — Example 3.5's morphism map.
* `piUnivHom` — Example 3.6's morphism map, the one that does not exist over
  `Set`.

## Main statements

* `FamHom.id_comp` / `comp_id` / `comp_assoc` — `FamHom` composes as a category,
  and `FamHom.ext` is its extensionality.
* `univCodeMap_id` / `univCodeMap_comp` — the action on codes is functorial.
* `sigmaUnivHom_id` / `sigmaUnivHom_comp` / `piUnivHom_id` / `piUnivHom_comp` —
  both morphism maps are functorial, decoding components included.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [LindenhoviusMisloveZamdzhiev2021]

## Tags

prototype, inductive-recursive, universe, variance, split epimorphism,
embedding-projection pair
-/

@[expose] public section

namespace GebProto.UniverseVariance

/-! ## The ambient category -/

/-- An object of `Fam` over the split-epimorphism base: a type of codes together
with a decoding. -/
structure Fam : Type 1 where
  /-- The codes. -/
  Code : Type
  /-- The decoding. -/
  dec : Code → Type

/-- A morphism of families: a map of codes together with an
embedding-projection pair between each code's decoding and its image's. The
projection is what the dependent-product former runs the reindexing backwards
along. -/
structure FamHom (A B : Fam) : Type where
  /-- The map of codes. -/
  code : A.Code → B.Code
  /-- The embedding-projection pair at each code: the projection is the split
  epimorphism and the embedding its chosen section. -/
  ep : ∀ u, Split (B.dec (code u)) (A.dec u)

namespace FamHom

/-- The projection of a decoding onto its source. -/
def proj {A B : Fam} (m : FamHom A B) (u : A.Code) :
    B.dec (m.code u) → A.dec u :=
  (m.ep u).toFun

/-- The embedding of a decoding into its image's. -/
def emb {A B : Fam} (m : FamHom A B) (u : A.Code) :
    A.dec u → B.dec (m.code u) :=
  (m.ep u).sect

/-- The projection retracts the embedding. -/
theorem proj_emb {A B : Fam} (m : FamHom A B) (u : A.Code) (x : A.dec u) :
    m.proj u (m.emb u x) = x :=
  (m.ep u).toFun_sect x

/-- The identity morphism. -/
def id (A : Fam) : FamHom A A where
  code := _root_.id
  ep u := Split.id (A.dec u)

/-- Composition: the codes compose forwards and the embedding-projection pairs
compose as `Split`s, so the retraction is inherited. -/
def comp {A B C : Fam} (m : FamHom A B) (m' : FamHom B C) : FamHom A C where
  code := m'.code ∘ m.code
  ep u := (m'.ep (m.code u)).comp (m.ep u)

/-- Composition with the identity on the left. -/
theorem id_comp {A B : Fam} (m : FamHom A B) : (FamHom.id A).comp m = m := rfl

/-- Composition with the identity on the right. -/
theorem comp_id {A B : Fam} (m : FamHom A B) : m.comp (FamHom.id B) = m := rfl

/-- Two morphisms of families with the same code map and the same
embedding-projection pair at each code are equal. -/
theorem ext {A B : Fam} {m m' : FamHom A B} (h : m.code = m'.code)
    (h' : ∀ u, m.ep u ≍ m'.ep u) : m = m' := by
  cases m with
  | mk c e =>
    cases m' with
    | mk c' e' =>
      cases h
      exact congrArg (FamHom.mk c) (funext fun u ↦ eq_of_heq (h' u))

/-- Composition is associative. -/
theorem comp_assoc {A B C D : Fam} (m : FamHom A B) (m' : FamHom B C)
    (m'' : FamHom C D) : (m.comp m').comp m'' = m.comp (m'.comp m'') := rfl

end FamHom

/-! ## The universe functor on objects -/

/-- The codes of the universe: one nullary code for the base type, and one
binder code per code and family of codes indexed by its decoding. -/
def UnivCode (A : Fam) : Type :=
  Unit ⊕ Σ u : A.Code, (A.dec u → A.Code)

/-- The decoding of the universe's codes, at a base type and a type former. -/
def univDec (base : Type) (former : (S : Type) → (S → Type) → Type) (A : Fam) :
    UnivCode A → Type
  | .inl _ => base
  | .inr ⟨u, v⟩ => former (A.dec u) (fun x ↦ A.dec (v x))

/-- The universe functor on objects. -/
def univObj (base : Type) (former : (S : Type) → (S → Type) → Type) (A : Fam) :
    Fam where
  Code := UnivCode A
  dec := univDec base former A

/-- The action on codes: the bound code goes forward and the binder's family is
reindexed along the projection. This is the `replace` of the discrete
presentation. -/
def univCodeMap {A B : Fam} (m : FamHom A B) : UnivCode A → UnivCode B
  | .inl _ => .inl ()
  | .inr ⟨u, v⟩ => .inr ⟨m.code u, fun y ↦ m.code (v (m.proj u y))⟩

/-- The action on codes preserves the identity. -/
theorem univCodeMap_id (A : Fam) :
    univCodeMap (FamHom.id A) = _root_.id := by
  funext c
  cases c <;> rfl

/-- The action on codes preserves composition: the two reindexings of the
binder's family along the projections compose. -/
theorem univCodeMap_comp {A B C : Fam} (m : FamHom A B) (m' : FamHom B C) :
    univCodeMap (m.comp m') = univCodeMap m' ∘ univCodeMap m := by
  funext c
  cases c <;> rfl

/-! ## Example 3.5: the dependent-sum universe -/

/-- The dependent-sum former. -/
def sigmaFormer : (S : Type) → (S → Type) → Type :=
  fun S T ↦ Σ x : S, T x

/-- The morphism map of the dependent-sum universe. The embedding pairs the
embedded index with the embedded value, transported across the reindexing of the
family; the projection needs no transport. -/
def sigmaUnivHom {A B : Fam} (base : Type) (m : FamHom A B) :
    FamHom (univObj base sigmaFormer A) (univObj base sigmaFormer B) where
  code := univCodeMap m
  ep
    | .inl _ => Split.id base
    | .inr ⟨u, v⟩ => sigmaSplit (m.ep u) fun y ↦ m.ep (v (m.proj u y))

/-- The dependent-sum universe's morphism map preserves the identity. -/
theorem sigmaUnivHom_id (base : Type) (A : Fam) :
    sigmaUnivHom base (FamHom.id A) = FamHom.id (univObj base sigmaFormer A) :=
  FamHom.ext (univCodeMap_id A) fun c ↦ by
    match c with
    | .inl _ => rfl
    | .inr ⟨_, _⟩ => exact heq_of_eq (sigmaSplit_id _)

/-- The dependent-sum universe's morphism map preserves composition, decoding
components included: `sigmaSplit_comp` at each binder code. -/
theorem sigmaUnivHom_comp {A B C : Fam} (base : Type) (m : FamHom A B) (m' : FamHom B C) :
    sigmaUnivHom base (m.comp m') = (sigmaUnivHom base m).comp (sigmaUnivHom base m') :=
  FamHom.ext (univCodeMap_comp m m') fun c ↦ by
    match c with
    | .inl _ => rfl
    | .inr ⟨u, v⟩ =>
      exact heq_of_eq (sigmaSplit_comp
        (Y := fun x ↦ A.dec (v x))
        (Y' := fun y ↦ B.dec (m.code (v (m.proj u y))))
        (Y'' := fun z ↦ C.dec (m'.code (m.code (v (m.proj u (m'.proj (m.code u) z))))))
        (m'.ep (m.code u)) (m.ep u)
        (fun y ↦ m.ep (v (m.proj u y)))
        (fun z ↦ m'.ep (m.code (v (m.proj u (m'.proj (m.code u) z))))))

/-! ## Example 3.6: the dependent-product universe

The morphism map the paper shows does not exist over `Set`: its embedding
evaluates the given section family at the projection, and its projection runs
the reindexing backwards along the embedding. Neither is available without the
section. -/

/-- The dependent-product former. -/
def piFormer : (S : Type) → (S → Type) → Type :=
  fun S T ↦ (x : S) → T x

/-- The morphism map of the dependent-product universe. -/
def piUnivHom {A B : Fam} (base : Type) (m : FamHom A B) :
    FamHom (univObj base piFormer A) (univObj base piFormer B) where
  code := univCodeMap m
  ep
    | .inl _ => Split.id base
    | .inr ⟨u, v⟩ => piSplit (m.ep u) fun y ↦ m.ep (v (m.proj u y))

/-- The dependent-product universe's morphism map preserves the identity. -/
theorem piUnivHom_id (base : Type) (A : Fam) :
    piUnivHom base (FamHom.id A) = FamHom.id (univObj base piFormer A) :=
  FamHom.ext (univCodeMap_id A) fun c ↦ by
    match c with
    | .inl _ => rfl
    | .inr ⟨_, _⟩ => exact heq_of_eq (piSplit_id _)

/-- The dependent-product universe's morphism map preserves composition, decoding
components included: `piSplit_comp` at each binder code. -/
theorem piUnivHom_comp {A B C : Fam} (base : Type) (m : FamHom A B) (m' : FamHom B C) :
    piUnivHom base (m.comp m') = (piUnivHom base m).comp (piUnivHom base m') :=
  FamHom.ext (univCodeMap_comp m m') fun c ↦ by
    match c with
    | .inl _ => rfl
    | .inr ⟨u, v⟩ =>
      exact heq_of_eq (piSplit_comp
        (Y := fun x ↦ A.dec (v x))
        (Y' := fun y ↦ B.dec (m.code (v (m.proj u y))))
        (Y'' := fun z ↦ C.dec (m'.code (m.code (v (m.proj u (m'.proj (m.code u) z))))))
        (m'.ep (m.code u)) (m.ep u)
        (fun y ↦ m.ep (v (m.proj u y)))
        (fun z ↦ m'.ep (m.code (v (m.proj u (m'.proj (m.code u) z))))))

end GebProto.UniverseVariance
