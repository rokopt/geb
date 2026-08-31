/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.Grothendieck.Basic

/-!
# Functors into a Grothendieck construction

For `F : C ⥤ Cat`, a functor `D ⥤ Grothendieck F` amounts to a base functor
`D ⥤ C` together with a fiber object over each object of `D` and a fiber
morphism over each morphism of `D`, subject to identity and composition
coherence; a natural transformation of two such functors amounts to a
transformation of base functors and a fiber morphism over each object of `D`.
This module bundles each family of data as a structure, gives the data a
category structure whose morphisms are the bundled transformations, and
identifies that category with the functor category. The contravariant
construction is treated alongside the covariant one.

## Main definitions

* `CategoryTheory.Grothendieck.FunctorToData` and `Grothendieck.functorTo`
* `CategoryTheory.Grothendieck.NatTransToData` and `Grothendieck.natTransTo`
* `CategoryTheory.Grothendieck.FunctorToData.precomp`
* `CategoryTheory.CoGrothendieck.FunctorToData`, with the constructor
  `FunctorToData.mk` and its accessors, and `CoGrothendieck.functorTo`

## Main statements

* `Grothendieck.functorToEquiv` and `Grothendieck.natTransToEquiv`: the data
  determines the functor, and the transformation data determines the
  transformation, bijectively
* `Grothendieck.functorToDataIsoCat` and `CoGrothendieck.functorToDataIsoCat`:
  the category of data is isomorphic to the functor category

## Implementation notes

The correspondence is an isomorphism of categories, not merely an equivalence,
because both round trips hold by `rfl`: a `FunctorToData` is the fields of a
functor into `Grothendieck F` with the base and fiber projections distributed
over the components.

`NatTransToFibNat` states its two routes as morphisms out of the pushforward
along `baseNat.app d ≫ dataH.baseFunc.map f`. That is the basepoint at which
`Grothendieck.ext` leaves the fiber goal; stating the condition at the
domain-side composite instead differs from it by a transport along
`baseNat.naturality`, which no unfolding closes.

The contravariant data type is the covariant one for `G ⋙ Cat.opFunctor`,
taken in the opposite category so that its transformations run in the direction
of the domain, with a constructor and accessors phrased in terms of morphisms
of `C` as in `Geb/Mathlib/CategoryTheory/Grothendieck/Basic.lean`. The
transport costs nothing definitionally: `Functor.rightOpLeftOpIso` and
`Functor.leftOpRightOpIso` are `Iso.refl`, so the isomorphism of categories
survives the passage to the contravariant side.

`Cat` is a semireducible `def` whose morphisms are a bundled `Cat.Hom`, so
keyed `simp`/`rw` matching fails against generic lemmas on terms routed through
`F.obj`/`F.map` even where the two sides are definitionally equal; see
`Geb/Mathlib/CategoryTheory/Grothendieck/Basic.lean` § Implementation notes.
The `erw` steps below isolate exactly those crossings.

## References

The Grothendieck construction is standard; see [Vistoli2008] and
[JohnsonYau2021].

## Tags

Grothendieck construction, contravariant, functor category, universal property
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆

namespace CategoryTheory

open CategoryTheory.Functor

namespace Grothendieck

variable {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{v₂, u₂})
variable {D : Type u₁} [Category.{v₁} D]

/-! ### Functors into a covariant Grothendieck construction -/

/-- The fiber-object component of the data determining a functor into
`Grothendieck F` with base functor `baseFunc`: an object of the fiber over
`baseFunc.obj d` for each `d`. -/
abbrev FunctorToFib (baseFunc : D ⥤ C) := ∀ d, F.obj (baseFunc.obj d)

/-- The fiber-morphism component of the data determining a functor into
`Grothendieck F`: for each `g : d ⟶ d'`, a morphism from the pushforward of the
source fiber object to the target fiber object. -/
abbrev FunctorToHom (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :=
  ∀ {d d' : D} (g : d ⟶ d'),
    (F.map (baseFunc.map g)).toFunctor.obj (fib d) ⟶ fib d'

/-- The identity coherence condition on the fiber-morphism component: the fiber
morphism over an identity is the canonical transport isomorphism. -/
abbrev FunctorToHomId (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc)
    (hom : FunctorToHom F baseFunc fib) :=
  ∀ d, hom (𝟙 d) = eqToHom (by simp only [CategoryTheory.Functor.map_id]; rfl)

/-- The composition coherence condition on the fiber-morphism component: the
fiber morphism over a composite factors through the pushforward of the fiber
morphism over the first factor. -/
abbrev FunctorToHomComp (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc)
    (hom : FunctorToHom F baseFunc fib) :=
  ∀ {d d' d'' : D} (g : d ⟶ d') (h : d' ⟶ d''),
    hom (g ≫ h) = eqToHom (by simp only [CategoryTheory.Functor.map_comp]; rfl) ≫
      (F.map (baseFunc.map h)).toFunctor.map (hom g) ≫ hom h

variable (D) in
/-- The data determining a functor `D ⥤ Grothendieck F`: a base functor, a
fiber object over each object of `D`, a fiber morphism over each morphism of
`D`, and the two coherence conditions. -/
structure FunctorToData : Type (max u v u₁ v₁ u₂ v₂) where
  /-- The base functor. -/
  baseFunc : D ⥤ C
  /-- The fiber object over each object of `D`. -/
  fib : FunctorToFib F baseFunc
  /-- The fiber morphism over each morphism of `D`. -/
  hom : FunctorToHom F baseFunc fib
  /-- Identity coherence. -/
  hom_id : FunctorToHomId F baseFunc fib hom
  /-- Composition coherence. -/
  hom_comp : FunctorToHomComp F baseFunc fib hom

variable {F}

/-- The functor `D ⥤ Grothendieck F` determined by a `FunctorToData`. -/
def functorTo (data : FunctorToData F D) : D ⥤ Grothendieck F where
  obj d := ⟨data.baseFunc.obj d, data.fib d⟩
  map g := ⟨data.baseFunc.map g, data.hom g⟩
  map_id d := Grothendieck.ext _ _ (data.baseFunc.map_id d) (by
    simp only [Grothendieck.id_fiber, data.hom_id, eqToHom_trans])
  map_comp g h := Grothendieck.ext _ _ (data.baseFunc.map_comp g h) (by
    simp only [Grothendieck.comp_fiber, data.hom_comp, ← Category.assoc, eqToHom_trans])

/-- The functor determined by a `FunctorToData` lies over its base functor. -/
theorem functorTo_comp_forget (data : FunctorToData F D) :
    functorTo data ⋙ Grothendieck.forget F = data.baseFunc :=
  rfl

/-- The `FunctorToData` determined by a functor `D ⥤ Grothendieck F`. -/
def ofFunctor (G : D ⥤ Grothendieck F) : FunctorToData F D where
  baseFunc := G ⋙ Grothendieck.forget F
  fib d := (G.obj d).fiber
  hom g := (G.map g).fiber
  hom_id d := by
    beta_reduce
    rw [Grothendieck.congr (G.map_id d), Grothendieck.id_fiber, eqToHom_trans]
    rfl
  hom_comp g h := by
    beta_reduce
    rw [Grothendieck.congr (G.map_comp g h), Grothendieck.comp_fiber, ← Category.assoc,
      eqToHom_trans]
    rfl

/-- Building a functor from the data extracted from it recovers the functor. -/
theorem functorTo_ofFunctor (G : D ⥤ Grothendieck F) : functorTo (ofFunctor G) = G :=
  rfl

/-- Extracting the data from the functor built on it recovers the data. -/
theorem ofFunctor_functorTo (data : FunctorToData F D) :
    ofFunctor (functorTo data) = data :=
  rfl

/-- Functors `D ⥤ Grothendieck F` correspond to their determining data. -/
def functorToEquiv : (D ⥤ Grothendieck F) ≃ FunctorToData F D where
  toFun := ofFunctor
  invFun := functorTo
  left_inv := functorTo_ofFunctor
  right_inv := ofFunctor_functorTo

variable {D' : Type u₄} [Category.{v₄} D']

/-- Precomposition of the data determining a functor into `Grothendieck F` with
a functor into its domain. -/
def FunctorToData.precomp (data : FunctorToData F D) (K : D' ⥤ D) :
    FunctorToData F D' :=
  ofFunctor (K ⋙ functorTo data)

/-- `functorTo` turns precomposition of data into precomposition of functors. -/
@[simp]
theorem functorTo_precomp (data : FunctorToData F D) (K : D' ⥤ D) :
    functorTo (data.precomp K) = K ⋙ functorTo data :=
  rfl

/-- The base functor of precomposed data is the precomposed base functor. -/
@[simp]
theorem precomp_baseFunc (data : FunctorToData F D) (K : D' ⥤ D) :
    (data.precomp K).baseFunc = K ⋙ data.baseFunc :=
  rfl

/-! ### Natural transformations of functors into a covariant Grothendieck construction -/

variable (F)

/-- The fiber-morphism component of the data determining a natural transformation
between functors into `Grothendieck F`: for each `d`, a morphism from the
pushforward of the source fiber object along the base transformation to the
target fiber object. -/
abbrev NatTransToFibMor (dataG dataH : FunctorToData F D)
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc) :=
  ∀ d, (F.map (baseNat.app d)).toFunctor.obj (dataG.fib d) ⟶ dataH.fib d

/-- The naturality condition on the fiber-morphism component: the two routes
around the fiber square agree, both read as morphisms out of the pushforward
along `baseNat.app d ≫ dataH.baseFunc.map f`. -/
abbrev NatTransToFibNat (dataG dataH : FunctorToData F D)
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc)
    (fibMor : NatTransToFibMor F dataG dataH baseNat) :=
  ∀ {d d' : D} (f : d ⟶ d'),
    eqToHom ((congrArg (fun p ↦ (F.map p).toFunctor.obj (dataG.fib d))
          (baseNat.naturality f)).symm.trans (Functor.congr_obj
        congr($(F.map_comp (dataG.baseFunc.map f) (baseNat.app d')).toFunctor)
        (dataG.fib d))) ≫
      (F.map (baseNat.app d')).toFunctor.map (dataG.hom f) ≫ fibMor d' =
    eqToHom (Functor.congr_obj
        congr($(F.map_comp (baseNat.app d) (dataH.baseFunc.map f)).toFunctor)
        (dataG.fib d)) ≫
      (F.map (dataH.baseFunc.map f)).toFunctor.map (fibMor d) ≫ dataH.hom f

/-- The data determining a natural transformation between functors into
`Grothendieck F`: a transformation of base functors, a fiber morphism over each
object of `D`, and the fiber naturality condition. -/
@[ext]
structure NatTransToData (dataG dataH : FunctorToData F D) : Type (max u₁ v v₂) where
  /-- The transformation of base functors. -/
  baseNat : dataG.baseFunc ⟶ dataH.baseFunc
  /-- The fiber morphism over each object of `D`. -/
  fibMor : NatTransToFibMor F dataG dataH baseNat
  /-- Fiber naturality. -/
  fibNat : NatTransToFibNat F dataG dataH baseNat fibMor

variable {F}

/-- The natural transformation determined by a `NatTransToData`. -/
def natTransTo {dataG dataH : FunctorToData F D} (nat : NatTransToData F dataG dataH) :
    functorTo dataG ⟶ functorTo dataH where
  app d := ⟨nat.baseNat.app d, nat.fibMor d⟩
  naturality {_ _} f := by
    refine Grothendieck.ext _ _ (nat.baseNat.naturality f) ?_
    simp only [Grothendieck.comp_fiber, eqToHom_trans_assoc]
    exact nat.fibNat f

/-- The `NatTransToData` determined by a natural transformation between functors
into `Grothendieck F`. -/
def ofNatTrans {dataG dataH : FunctorToData F D}
    (α : functorTo dataG ⟶ functorTo dataH) : NatTransToData F dataG dataH where
  baseNat :=
    { app := fun d ↦ (α.app d).base
      naturality := fun {_ _} f ↦ congrArg Grothendieck.Hom.base (α.naturality f) }
  fibMor d := (α.app d).fiber
  fibNat {_ _} f := by
    have h := Grothendieck.congr (α.naturality f).symm
    simp only [Grothendieck.comp_fiber, eqToHom_trans_assoc] at h
    exact h.symm

/-- Building a natural transformation from the data extracted from it recovers
the transformation. -/
theorem natTransTo_ofNatTrans {dataG dataH : FunctorToData F D}
    (α : functorTo dataG ⟶ functorTo dataH) : natTransTo (ofNatTrans α) = α :=
  rfl

/-- Extracting the data from the natural transformation built on it recovers the
data. -/
theorem ofNatTrans_natTransTo {dataG dataH : FunctorToData F D}
    (nat : NatTransToData F dataG dataH) : ofNatTrans (natTransTo nat) = nat :=
  rfl

/-- Natural transformations between functors into `Grothendieck F` correspond to
their determining data. -/
def natTransToEquiv (dataG dataH : FunctorToData F D) :
    NatTransToData F dataG dataH ≃ (functorTo dataG ⟶ functorTo dataH) where
  toFun := natTransTo
  invFun := ofNatTrans
  left_inv := ofNatTrans_natTransTo
  right_inv := natTransTo_ofNatTrans

/-- The identity transformation of a `FunctorToData`. -/
def NatTransToData.id (data : FunctorToData F D) : NatTransToData F data data :=
  ofNatTrans (𝟙 (functorTo data))

/-- Composition of transformations of `FunctorToData`. -/
def NatTransToData.comp {dataG dataH dataK : FunctorToData F D}
    (nat₁ : NatTransToData F dataG dataH) (nat₂ : NatTransToData F dataH dataK) :
    NatTransToData F dataG dataK :=
  ofNatTrans (natTransTo nat₁ ≫ natTransTo nat₂)

variable (F) in
/-- The category of data determining functors `D ⥤ Grothendieck F`. -/
instance functorToDataCategory : Category.{max u₁ v v₂} (FunctorToData F D) where
  Hom := NatTransToData F
  id := NatTransToData.id
  comp := NatTransToData.comp
  id_comp nat := by
    unfold NatTransToData.id NatTransToData.comp
    conv_rhs => rw [← ofNatTrans_natTransTo nat]
    congr 1
    exact Category.id_comp _
  comp_id nat := by
    unfold NatTransToData.id NatTransToData.comp
    conv_rhs => rw [← ofNatTrans_natTransTo nat]
    congr 1
    exact Category.comp_id _
  assoc nat₁ nat₂ nat₃ := by
    unfold NatTransToData.comp
    congr 1
    exact Category.assoc _ _ _

variable (F D)

/-- The functor from the category of data to the functor category. -/
def functorToDataToFunctorCat : FunctorToData F D ⥤ (D ⥤ Grothendieck F) where
  obj := functorTo
  map := natTransTo
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from the functor category to the category of data. -/
def functorCatToFunctorToData : (D ⥤ Grothendieck F) ⥤ FunctorToData F D where
  obj := ofFunctor
  map {G H} α := ofNatTrans (dataG := ofFunctor G) (dataH := ofFunctor H) α
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of data determining functors `D ⥤ Grothendieck F` is isomorphic
to the functor category. -/
def functorToDataIsoCat :
    Cat.of (FunctorToData F D) ≅ Cat.of (D ⥤ Grothendieck F) where
  hom := (functorToDataToFunctorCat F D).toCatHom
  inv := (functorCatToFunctorToData F D).toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

end Grothendieck

namespace CoGrothendieck

variable {C : Type u} [Category.{v} C] (G : Cᵒᵖ ⥤ Cat.{v₂, u₂})
variable {E : Type u₁} [Category.{v₁} E]

/-! ### Functors into a contravariant Grothendieck construction -/

/-- The fiber-object component of the data determining a functor into
`CoGrothendieck G` with base functor `baseFunc`: an object of the fiber over
`baseFunc.obj e` for each `e`. -/
abbrev FunctorToFib (baseFunc : E ⥤ C) := ∀ e, G.obj (Opposite.op (baseFunc.obj e))

/-- The fiber-morphism component of the data determining a functor into
`CoGrothendieck G`: for each `g : e ⟶ e'`, a morphism from the source fiber
object to the pullback of the target fiber object. -/
abbrev FunctorToHom (baseFunc : E ⥤ C) (fib : FunctorToFib G baseFunc) :=
  ∀ {e e' : E} (g : e ⟶ e'),
    fib e ⟶ (G.map (baseFunc.map g).op).toFunctor.obj (fib e')

/-- The identity coherence condition on the fiber-morphism component. -/
abbrev FunctorToHomId (baseFunc : E ⥤ C) (fib : FunctorToFib G baseFunc)
    (hom : FunctorToHom G baseFunc fib) :=
  ∀ e, hom (𝟙 e) =
    eqToHom (by simp only [CategoryTheory.Functor.map_id, op_id]; rfl)

/-- The composition coherence condition on the fiber-morphism component. -/
abbrev FunctorToHomComp (baseFunc : E ⥤ C) (fib : FunctorToFib G baseFunc)
    (hom : FunctorToHom G baseFunc fib) :=
  ∀ {e e' e'' : E} (g : e ⟶ e') (h : e' ⟶ e''),
    hom (g ≫ h) = hom g ≫ (G.map (baseFunc.map g).op).toFunctor.map (hom h) ≫
      eqToHom (by simp only [CategoryTheory.Functor.map_comp, op_comp]; rfl)

variable (E) in
/-- The data determining a functor `E ⥤ CoGrothendieck G`: the data determining
the corresponding functor `Eᵒᵖ ⥤ GrothendieckOp G`, taken in the opposite
category so that its transformations run in the direction of `E`. -/
@[implicit_reducible]
def FunctorToData : Type (max u v u₁ v₁ u₂ v₂) :=
  (Grothendieck.FunctorToData (G ⋙ Cat.opFunctor) Eᵒᵖ)ᵒᵖ

/-- The category structure on the data determining functors
`E ⥤ CoGrothendieck G`, inherited from the opposite of the covariant one. -/
instance functorToDataCategory : Category.{max u₁ v v₂} (FunctorToData G E) :=
  inferInstanceAs
    (Category (Grothendieck.FunctorToData (G ⋙ Cat.opFunctor) Eᵒᵖ)ᵒᵖ)

variable {G}

/-- Construct the data determining a functor `E ⥤ CoGrothendieck G` from a base
functor, a fiber object over each object of `E`, a fiber morphism over each
morphism of `E`, and the two coherence conditions. -/
def FunctorToData.mk (baseFunc : E ⥤ C) (fib : FunctorToFib G baseFunc)
    (hom : FunctorToHom G baseFunc fib)
    (hom_id : FunctorToHomId G baseFunc fib hom)
    (hom_comp : FunctorToHomComp G baseFunc fib hom) : FunctorToData G E :=
  Opposite.op
    { baseFunc := baseFunc.op
      fib := fun e ↦ Opposite.op (fib e.unop)
      hom := fun g ↦ Quiver.Hom.op (hom g.unop)
      hom_id := fun e ↦ by
        apply Quiver.Hom.unop_inj
        erw [eqToHom_unop]
        exact hom_id e.unop
      hom_comp := fun g h ↦ by
        apply Quiver.Hom.unop_inj
        erw [unop_comp, unop_comp, eqToHom_unop, Category.assoc]
        exact hom_comp h.unop g.unop }

/-- The base functor of the data determining a functor `E ⥤ CoGrothendieck G`. -/
def FunctorToData.baseFunc (data : FunctorToData G E) : E ⥤ C :=
  data.unop.baseFunc.unop

/-- The fiber object over each object of `E`. -/
def FunctorToData.fib (data : FunctorToData G E) :
    FunctorToFib G data.baseFunc :=
  fun e ↦ Opposite.unop (data.unop.fib (Opposite.op e))

/-- The fiber morphism over each morphism of `E`. -/
def FunctorToData.hom (data : FunctorToData G E) :
    FunctorToHom G data.baseFunc data.fib :=
  fun g ↦ Quiver.Hom.unop (data.unop.hom (Quiver.Hom.op g))

/-- `FunctorToData.mk` recovers the base functor on the nose. -/
@[simp]
theorem FunctorToData.baseFunc_mk (baseFunc : E ⥤ C)
    (fib : FunctorToFib G baseFunc) (hom : FunctorToHom G baseFunc fib)
    (hom_id : FunctorToHomId G baseFunc fib hom)
    (hom_comp : FunctorToHomComp G baseFunc fib hom) :
    (FunctorToData.mk baseFunc fib hom hom_id hom_comp).baseFunc = baseFunc :=
  rfl

/-- `FunctorToData.mk` recovers the fiber objects on the nose. -/
@[simp]
theorem FunctorToData.fib_mk (baseFunc : E ⥤ C) (fib : FunctorToFib G baseFunc)
    (hom : FunctorToHom G baseFunc fib)
    (hom_id : FunctorToHomId G baseFunc fib hom)
    (hom_comp : FunctorToHomComp G baseFunc fib hom) (e : E) :
    (FunctorToData.mk baseFunc fib hom hom_id hom_comp).fib e = fib e :=
  rfl

/-- `FunctorToData.mk` recovers the fiber morphisms on the nose. -/
@[simp]
theorem FunctorToData.hom_mk (baseFunc : E ⥤ C) (fib : FunctorToFib G baseFunc)
    (hom : FunctorToHom G baseFunc fib)
    (hom_id : FunctorToHomId G baseFunc fib hom)
    (hom_comp : FunctorToHomComp G baseFunc fib hom) {e e' : E} (g : e ⟶ e') :
    (FunctorToData.mk baseFunc fib hom hom_id hom_comp).hom g = hom g :=
  rfl

/-- The functor `E ⥤ CoGrothendieck G` determined by a `FunctorToData`. -/
def functorTo (data : FunctorToData G E) : E ⥤ CoGrothendieck G :=
  (Grothendieck.functorTo data.unop).rightOp

/-- The `FunctorToData` determined by a functor `E ⥤ CoGrothendieck G`. -/
def ofFunctor (K : E ⥤ CoGrothendieck G) : FunctorToData G E :=
  Opposite.op (Grothendieck.ofFunctor K.leftOp)

/-- Building a functor from the data extracted from it recovers the functor. -/
theorem functorTo_ofFunctor (K : E ⥤ CoGrothendieck G) :
    functorTo (ofFunctor K) = K :=
  rfl

/-- Extracting the data from the functor built on it recovers the data. -/
theorem ofFunctor_functorTo (data : FunctorToData G E) :
    ofFunctor (functorTo data) = data :=
  rfl

/-- Functors `E ⥤ CoGrothendieck G` correspond to their determining data. -/
def functorToEquiv : (E ⥤ CoGrothendieck G) ≃ FunctorToData G E where
  toFun := ofFunctor
  invFun := functorTo
  left_inv := functorTo_ofFunctor
  right_inv := ofFunctor_functorTo

/-- The functor determined by a `FunctorToData` sends an object of `E` to the
pair of its base and fiber components. -/
@[simp]
theorem functorTo_obj (data : FunctorToData G E) (e : E) :
    (functorTo data).obj e =
      CoGrothendieck.mk (data.baseFunc.obj e) (data.fib e) :=
  rfl

/-- The natural transformation determined by a morphism of the data. -/
def natTransTo {dataG dataH : FunctorToData G E} (nat : dataG ⟶ dataH) :
    functorTo dataG ⟶ functorTo dataH :=
  NatTrans.rightOp (Grothendieck.natTransTo nat.unop)

/-- The morphism of data determined by a natural transformation. -/
def ofNatTrans {dataG dataH : FunctorToData G E}
    (α : functorTo dataG ⟶ functorTo dataH) : dataG ⟶ dataH :=
  Quiver.Hom.op (Grothendieck.ofNatTrans (NatTrans.leftOp α))

/-- Building a natural transformation from the data extracted from it recovers
the transformation. -/
theorem natTransTo_ofNatTrans {dataG dataH : FunctorToData G E}
    (α : functorTo dataG ⟶ functorTo dataH) : natTransTo (ofNatTrans α) = α :=
  rfl

/-- Extracting the data from the natural transformation built on it recovers the
data. -/
theorem ofNatTrans_natTransTo {dataG dataH : FunctorToData G E}
    (nat : dataG ⟶ dataH) : ofNatTrans (natTransTo nat) = nat :=
  rfl

/-- Natural transformations between functors into `CoGrothendieck G` correspond
to the morphisms of their determining data. -/
def natTransToEquiv (dataG dataH : FunctorToData G E) :
    (dataG ⟶ dataH) ≃ (functorTo dataG ⟶ functorTo dataH) where
  toFun := natTransTo
  invFun := ofNatTrans
  left_inv := ofNatTrans_natTransTo
  right_inv := natTransTo_ofNatTrans

variable (G E)

/-- The functor from the category of data determining functors
`E ⥤ CoGrothendieck G` to that functor category. -/
def functorToDataToFunctorCat : FunctorToData G E ⥤ (E ⥤ CoGrothendieck G) where
  obj := functorTo
  map := natTransTo
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from the functor category to the category of data. -/
def functorCatToFunctorToData : (E ⥤ CoGrothendieck G) ⥤ FunctorToData G E where
  obj := ofFunctor
  map {K L} α := ofNatTrans (dataG := ofFunctor K) (dataH := ofFunctor L) α
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of data determining functors `E ⥤ CoGrothendieck G` is
isomorphic to that functor category. -/
def functorToDataIsoCat :
    Cat.of (FunctorToData G E) ≅ Cat.of (E ⥤ CoGrothendieck G) where
  hom := (functorToDataToFunctorCat G E).toCatHom
  inv := (functorCatToFunctorToData G E).toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

variable {G E}

variable {E' : Type u₄} [Category.{v₄} E']

/-- Precomposition of the data determining a functor into `CoGrothendieck G`
with a functor into its domain. -/
def FunctorToData.precomp (data : FunctorToData G E) (K : E' ⥤ E) :
    FunctorToData G E' :=
  ofFunctor (K ⋙ functorTo data)

/-- `functorTo` turns precomposition of data into precomposition of functors. -/
@[simp]
theorem functorTo_precomp (data : FunctorToData G E) (K : E' ⥤ E) :
    functorTo (data.precomp K) = K ⋙ functorTo data :=
  rfl


end CoGrothendieck

end CategoryTheory
