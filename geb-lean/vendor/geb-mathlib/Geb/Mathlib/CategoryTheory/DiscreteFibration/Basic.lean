/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Tactic.Attr.Core

/-!
# Discrete fibrations: lifting data

A functor `p : C ⥤ B` is a discrete fibration when every `g : b ⟶ p.obj c`
has a unique lift with codomain `c` ([LoregianRiehl2018] § 2.1;
[nLabDiscreteFibration]).  This module carries that lifting data as a
structure and relates it to mathlib's fibred-category API.

## Main definitions

* `DiscreteFibration p`, the lifting data: for each `g : b ⟶ p.obj c` a
  lift `hom g : src g ⟶ c`, together with the statement that it is the
  only lift.

## Main statements

* `DiscreteFibration.map_injective` and `DiscreteFibration.faithful`: a
  discrete fibration is faithful.
* `isHomLift_iff_arrow_mk_eq`: mathlib's `Functor.IsHomLift` is equality
  of arrows.
* `DiscreteFibration.isCartesian`, `DiscreteFibration.isPreFibered` and
  `DiscreteFibration.isFibered`: every morphism is cartesian, so a
  discrete fibration is a fibred category.
* `DiscreteFibration.fiber_eq_of_hom` and
  `DiscreteFibration.fiber_hom_ext`: the fibres are discrete categories.

## Implementation notes

Lifts are unique, so `DiscreteFibration p` is a `Subsingleton`: carrying
it as data costs nothing, and it lets the fibre presheaf of
`Geb/Mathlib/CategoryTheory/DiscreteFibration/FiberPresheaf.lean` be
defined without `Classical.choice`.

`eq_of_isHomLift_id` and `fiber_eq_of_hom` route through
`Functor.Fiber.fiberInclusion` rather than the subtype projections of
`Functor.Fiber`, which is semireducible: a goal mentioning `b.1` is not
type-correct at implicit transparency and stops `rw` and `simp`.

## References

* [LoregianRiehl2018]
* [nLabDiscreteFibration]

## Tags

discrete fibration, fibred category, cartesian morphism, fibre
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]

/-- Lifting data for `p`: for every `g : b ⟶ p.obj c` a lift
`hom g : src g ⟶ c` over `g`, unique among all lifts.  The base-side
`eqToHom` is forced by the *bundle* presentation (objects of `C` are only
propositionally over `b`); it vanishes in the *family* presentation
`Functor.CoElements` below. -/
structure DiscreteFibration (p : C ⥤ B) where
  /-- Domain of the lift of `g`. -/
  src : ∀ {b : B} {c : C}, (b ⟶ p.obj c) → C
  /-- The lift of `g`. -/
  hom : ∀ {b : B} {c : C} (g : b ⟶ p.obj c), src g ⟶ c
  /-- The domain of the lift of `g` lies over the domain of `g`. -/
  obj_src : ∀ {b : B} {c : C} (g : b ⟶ p.obj c), p.obj (src g) = b
  /-- The lift of `g` lies over `g`. -/
  map_hom : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
    p.map (hom g) = eqToHom (obj_src g) ≫ g
  /-- Uniqueness of lifts, as an equality in `Σ c', c' ⟶ c`. -/
  unique : ∀ {b : B} {c : C} (g : b ⟶ p.obj c) {c' : C} (h : c' ⟶ c)
    (e : p.obj c' = b), p.map h = eqToHom e ≫ g →
      (⟨c', h⟩ : Σ c', c' ⟶ c) = ⟨src g, hom g⟩

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- The uniqueness clause with the source fixed: `p` reflects equality of
parallel arrows, i.e. `p` is faithful. -/
theorem map_injective {c c' : C} {h₁ h₂ : c' ⟶ c}
    (H : p.map h₁ = p.map h₂) : h₁ = h₂ := by
  have h := (D.unique (p.map h₂) h₁ rfl (by simpa using H)).trans
    (D.unique (p.map h₂) h₂ rfl (by simp)).symm
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2

/-- A discrete fibration is faithful. -/
theorem faithful : p.Faithful := ⟨fun H => D.map_injective H⟩

/-- Uniqueness of the source of a lift. -/
theorem src_eq {b : B} {c c' : C} (g : b ⟶ p.obj c) (h : c' ⟶ c)
    (e : p.obj c' = b) (H : p.map h = eqToHom e ≫ g) : D.src g = c' :=
  (congrArg Sigma.fst (D.unique g h e H)).symm

/-- The lift of an identity is an identity. -/
theorem src_id (c : C) : D.src (𝟙 (p.obj c)) = c :=
  D.src_eq _ (𝟙 c) rfl (by simp)

/-- Lifting data is unique: `DiscreteFibration p` is a mere proposition. -/
instance : Subsingleton (DiscreteFibration p) := by
  constructor
  intro D₁ D₂
  have h : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
      (⟨D₁.src g, D₁.hom g⟩ : Σ c', c' ⟶ c) =
        ⟨D₂.src g, D₂.hom g⟩ :=
    fun g => D₂.unique g (D₁.hom g) (D₁.obj_src g) (D₁.map_hom g)
  obtain ⟨src₁, hom₁, _, _, _⟩ := D₁
  obtain ⟨src₂, hom₂, _, _, _⟩ := D₂
  have hs : @src₁ = @src₂ := by
    funext b c g
    exact congrArg Sigma.fst (h g)
  subst hs
  have hh : @hom₁ = @hom₂ := by
    funext b c g
    exact eq_of_heq (Sigma.mk.inj_iff.1 (h g)).2
  subst hh
  rfl

end DiscreteFibration

/-! ### Mathlib's `IsHomLift` -/

/-- Mathlib's `IsHomLift` is the proposition
`Arrow.mk (p.map φ) = Arrow.mk f`. -/
theorem isHomLift_iff_arrow_mk_eq (p : C ⥤ B) {R S : B} {a b : C}
    (f : R ⟶ S) (φ : a ⟶ b) :
    p.IsHomLift f φ ↔ Arrow.mk (p.map φ) = Arrow.mk f := by
  constructor
  · intro h
    exact (Arrow.mk_eq_mk_iff _ _).2
      ⟨IsHomLift.domain_eq p f φ, IsHomLift.codomain_eq p f φ,
        IsHomLift.fac' p f φ⟩
  · intro h
    obtain ⟨hR, hS, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
    exact IsHomLift.of_fac' p f φ hR hS hf

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- The lift of `g` as an arrow of `C`. -/
def liftArrow {b : B} {c : C} (g : b ⟶ p.obj c) : Arrow C :=
  Arrow.mk (D.hom g)

/-- The image of the lift of `g` is `g`, as an equality of arrows. -/
theorem arrow_mk_map_hom {b : B} {c : C} (g : b ⟶ p.obj c) :
    Arrow.mk (p.map (D.hom g)) = Arrow.mk g :=
  (Arrow.mk_eq_mk_iff _ _).2 ⟨D.obj_src g, rfl, by simp [D.map_hom]⟩

/-- The lift of `g` lies over `g` in mathlib's sense. -/
theorem isHomLift_hom {b : B} {c : C} (g : b ⟶ p.obj c) :
    p.IsHomLift g (D.hom g) :=
  (isHomLift_iff_arrow_mk_eq p g (D.hom g)).2 (D.arrow_mk_map_hom g)

/-- Uniqueness of lifts, `Arrow`-style. -/
theorem eq_liftArrow {b : B} {c : C} (g : b ⟶ p.obj c) {c' : C}
    (h : c' ⟶ c) (hh : Arrow.mk (p.map h) = Arrow.mk g) :
    Arrow.mk h = D.liftArrow g := by
  obtain ⟨e, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 hh
  have hu := D.unique g h e (by simpa using hf)
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hu
  simp only [liftArrow]
  subst h1
  rw [eq_of_heq h2]

/-- A morphism lying over an identity has equal endpoints. -/
theorem eq_of_isHomLift_id {S : B} {a b : C} (ψ : a ⟶ b)
    [p.IsHomLift (𝟙 S) ψ] : a = b :=
  (D.src_eq (eqToHom (IsHomLift.codomain_eq p (𝟙 S) ψ).symm) ψ
      (IsHomLift.domain_eq p (𝟙 S) ψ)
      (by simpa using IsHomLift.fac' p (𝟙 S) ψ)).symm.trans
    (D.src_eq (eqToHom (IsHomLift.codomain_eq p (𝟙 S) ψ).symm) (𝟙 b)
      (IsHomLift.codomain_eq p (𝟙 S) ψ) (by simp))

/-- The endpoints of a morphism of a fibre agree.  With `fiber_hom_ext`
below, the fibres of a discrete fibration are discrete categories. -/
theorem fiber_eq_of_hom {S : B} {a b : p.Fiber S} (φ : a ⟶ b) : a = b :=
  Functor.Fiber.fiberInclusion_obj_inj
    (D.eq_of_isHomLift_id (S := S) (Functor.Fiber.fiberInclusion.map φ))

/-- Parallel morphisms of a fibre agree, since `p` is faithful. -/
theorem fiber_hom_ext {S : B} {a b : p.Fiber S} (φ ψ : a ⟶ b) : φ = ψ :=
  Functor.Fiber.hom_ext (D.map_injective
    ((IsHomLift.fac' p (𝟙 S) (Functor.Fiber.fiberInclusion.map φ)).trans
      (IsHomLift.fac' p (𝟙 S) (Functor.Fiber.fiberInclusion.map ψ)).symm))

/-- Every morphism over `f` is cartesian in mathlib's sense: uniqueness of
lifts supplies the universal property outright. -/
theorem isCartesian {R S : B} {a b : C} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsHomLift f φ] : p.IsCartesian f φ where
  universal_property {a'} φ' _ := by
    have key : (⟨a', φ'⟩ : Σ c, c ⟶ b) = ⟨a, φ⟩ :=
      (D.unique (f ≫ eqToHom (IsHomLift.codomain_eq p f φ).symm) φ'
          (IsHomLift.domain_eq p f φ')
          (by simpa using IsHomLift.fac' p f φ')).trans
        (D.unique (f ≫ eqToHom (IsHomLift.codomain_eq p f φ).symm) φ
          (IsHomLift.domain_eq p f φ)
          (by simpa using IsHomLift.fac' p f φ)).symm
    obtain ⟨ha, hφ⟩ := Sigma.mk.inj_iff.1 key
    subst ha
    obtain rfl := eq_of_heq hφ
    refine ⟨𝟙 _, ⟨IsHomLift.id (IsHomLift.domain_eq p f φ'),
      Category.id_comp _⟩, fun χ hχ => D.map_injective ?_⟩
    have := hχ.1
    rw [p.map_id]
    simpa using IsHomLift.fac' p (𝟙 R) χ

/-- Every object of `C` admits a cartesian lift of every morphism into its
image. -/
theorem isPreFibered : p.IsPreFibered where
  exists_isCartesian' f :=
    ⟨D.src f, D.hom f, have := D.isHomLift_hom f; D.isCartesian _ _⟩

/-- A discrete fibration is a fibred category. -/
theorem isFibered : p.IsFibered where
  toIsPreFibered := D.isPreFibered
  comp := by
    intro _ _ _ f g _ _ _ φ ψ _ _
    exact D.isCartesian (f ≫ g) (φ ≫ ψ)

end DiscreteFibration

end CategoryTheory
