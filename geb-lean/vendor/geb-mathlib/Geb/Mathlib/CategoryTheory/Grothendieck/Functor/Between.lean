/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.Grothendieck.Functor.From
public import Geb.Mathlib.CategoryTheory.Grothendieck.Functor.To

/-!
# Functors between Grothendieck constructions

A functor out of a Grothendieck construction is determined by the data of its
restriction to each fiber. When the codomain is itself a Grothendieck
construction, each such restriction is in turn determined by the data of a
functor into that construction, and each transition between restrictions by the
data of a transformation of those. Substituting the second description into the
first presents a functor between two Grothendieck constructions by data
throughout, and likewise for the transformations between them. This module
carries out that substitution for each of the four pairs of variances.

## Main definitions

* `CategoryTheory.FunctorCovToCovData` and `CategoryTheory.NatTransCovToCovData`
* `CategoryTheory.FunctorCovToContraData` and
  `CategoryTheory.NatTransCovToContraData`
* `CategoryTheory.FunctorContraToCovData` and
  `CategoryTheory.NatTransContraToCovData`
* `CategoryTheory.FunctorContraToContraData` and
  `CategoryTheory.NatTransContraToContraData`
* the category structure on each, `functorCovToCovDataCategory` and its three
  counterparts

## Main statements

* `functorCovToCovDataEquivFromData` and its three counterparts: each category
  of data is equivalent, by mutually inverse comparisons, to the category of
  data determining a functor out of the domain
* `functorCovToCovDataEquivCat`, `functorCovToContraDataEquivCat`,
  `functorContraToCovDataEquivCat` and `functorContraToContraDataEquivCat`: each
  category of data is equivalent to the corresponding functor category

## Implementation notes

Each comparison with the category of data determining a functor out of the
domain has identity unit and counit: refining the fiber component into
fiberwise data and coarsening it back are mutually inverse on the nose, because
`functorTo` and `ofFunctor`, and `natTransTo` and `ofNatTrans`, are mutually
inverse by `rfl` in both variances. The equivalence with the functor category
is then obtained by composing with the equivalence for functors out of the
domain, which is where the only non-strictness enters.

The four developments are written out rather than derived from a single
construction parameterised by the codomain's presentation. Such a
parameterisation makes the round trip `functorTo (data.precomp K) = K ⋙
functorTo data` propositional rather than definitional, which forces an
`eqToHom` into the client-facing coherence conditions; concretely, in both
variances that round trip is `rfl`.

## References

The Grothendieck construction and the description of functors out of it by
fiberwise data are standard; see [Vistoli2008] and [JohnsonYau2021].

## Tags

Grothendieck construction, contravariant, functor category, universal property
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆

namespace CategoryTheory

open CategoryTheory.Functor

section Between

variable {B : Type u₅} [Category.{v₅} B] {P : Type u₆} [Category.{v₆} P]

/-! #### From a covariant to a covariant Grothendieck construction -/

section FunctorCovToCov

variable (G : B ⥤ Cat.{v₂, u₂}) (F : P ⥤ Cat.{v₃, u₃})

/-- The fibrewise component of the data determining a functor
`Grothendieck G ⥤ Grothendieck F`: for each object of the base, the data
determining a functor from that fiber into `Grothendieck F`. -/
abbrev FunctorCovToCovFib := ∀ c : B, Grothendieck.FunctorToData F ↑(G.obj c)

/-- The family of fiber functors determined by a fibrewise component. -/
abbrev FunctorCovToCovFibFunctor (fibTo : FunctorCovToCovFib G F) :
    Grothendieck.FunctorFromFib G (Grothendieck F) :=
  fun c ↦ Grothendieck.functorTo (fibTo c)

/-- The transition component: for each morphism of the base, the data
determining a transformation from the fiber functor at its source to the fiber
functor at its target precomposed with the pushforward. -/
abbrev FunctorCovToCovHom (fibTo : FunctorCovToCovFib G F) :=
  ∀ {c c' : B} (f : c ⟶ c'), fibTo c ⟶ (fibTo c').precomp (G.map f).toFunctor

/-- The family of transitions determined by a transition component. -/
abbrev FunctorCovToCovHomNat (fibTo : FunctorCovToCovFib G F)
    (homNat : FunctorCovToCovHom G F fibTo) :
    Grothendieck.FunctorFromHom G (FunctorCovToCovFibFunctor G F fibTo) :=
  fun f ↦ Grothendieck.natTransTo (homNat f)

/-- The data determining a functor `Grothendieck G ⥤ Grothendieck F`. -/
structure FunctorCovToCovData : Type (max u₂ v₂ u₃ v₃ u₅ v₅ u₆ v₆) where
  /-- The data determining a functor out of each fiber. -/
  fibTo : FunctorCovToCovFib G F
  /-- The data determining the transition over each morphism of the base. -/
  homNat : FunctorCovToCovHom G F fibTo
  /-- Identity coherence. -/
  homNat_id : Grothendieck.FunctorFromHomId G
    (FunctorCovToCovFibFunctor G F fibTo)
    (FunctorCovToCovHomNat G F fibTo homNat)
  /-- Composition coherence. -/
  homNat_comp : Grothendieck.FunctorFromHomComp G
    (FunctorCovToCovFibFunctor G F fibTo)
    (FunctorCovToCovHomNat G F fibTo homNat)

variable {G F}

/-- The data determining a functor out of `Grothendieck G` underlying the
data determining a functor to `Grothendieck F`. -/
def FunctorCovToCovData.toFromData (data : FunctorCovToCovData G F) :
    Grothendieck.FunctorFromData G (Grothendieck F) where
  fib := FunctorCovToCovFibFunctor G F data.fibTo
  hom := FunctorCovToCovHomNat G F data.fibTo data.homNat
  hom_id := data.homNat_id
  hom_comp := data.homNat_comp

/-- The data determining a functor to `Grothendieck F` underlying the data
determining a functor out of `Grothendieck G`. -/
def FunctorCovToCovData.ofFromData
    (data : Grothendieck.FunctorFromData G (Grothendieck F)) :
    FunctorCovToCovData G F where
  fibTo c := Grothendieck.ofFunctor (data.fib c)
  homNat f := Grothendieck.ofNatTrans (data.hom f)
  homNat_id := data.hom_id
  homNat_comp := data.hom_comp

/-- Recovering the underlying data undoes its refinement. -/
theorem FunctorCovToCovData.toFromData_ofFromData
    (data : Grothendieck.FunctorFromData G (Grothendieck F)) :
    (FunctorCovToCovData.ofFromData data).toFromData = data :=
  rfl

/-- Refining the underlying data recovers the original. -/
theorem FunctorCovToCovData.ofFromData_toFromData
    (data : FunctorCovToCovData G F) :
    FunctorCovToCovData.ofFromData data.toFromData = data :=
  rfl

variable (G F)

/-- The fibrewise component of a transformation of the data. -/
abbrev NatTransCovToCovFib (dataG dataH : FunctorCovToCovData G F) :=
  ∀ c : B, dataG.fibTo c ⟶ dataH.fibTo c

/-- The family of transformations determined by a fibrewise component. -/
abbrev NatTransCovToCovFibNat (dataG dataH : FunctorCovToCovData G F)
    (fibNat : NatTransCovToCovFib G F dataG dataH) :
    Grothendieck.NatTransFromFib G dataG.toFromData dataH.toFromData :=
  fun c ↦ Grothendieck.natTransTo (fibNat c)

/-- The data determining a transformation of functors
`Grothendieck G ⥤ Grothendieck F`. -/
@[ext]
structure NatTransCovToCovData (dataG dataH : FunctorCovToCovData G F) :
    Type (max u₂ u₅ v₃ v₆) where
  /-- The data determining the transformation over each fiber. -/
  fibNat : NatTransCovToCovFib G F dataG dataH
  /-- Coherence with the transition data. -/
  coherence : Grothendieck.NatTransFromCoherence G dataG.toFromData
    dataH.toFromData (NatTransCovToCovFibNat G F dataG dataH fibNat)

variable {G F}

/-- The transformation of the underlying data. -/
def NatTransCovToCovData.toFromData {dataG dataH : FunctorCovToCovData G F}
    (nat : NatTransCovToCovData G F dataG dataH) :
    dataG.toFromData ⟶ dataH.toFromData where
  fibNat := NatTransCovToCovFibNat G F dataG dataH nat.fibNat
  coherence := nat.coherence

/-- The refinement of a transformation of the underlying data. -/
def NatTransCovToCovData.ofFromData {dataG dataH : FunctorCovToCovData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    NatTransCovToCovData G F dataG dataH where
  fibNat c := Grothendieck.ofNatTrans (nat.fibNat c)
  coherence := nat.coherence

/-- Recovering the underlying transformation undoes its refinement. -/
theorem NatTransCovToCovData.toFromData_ofFromData
    {dataG dataH : FunctorCovToCovData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    (NatTransCovToCovData.ofFromData nat).toFromData = nat :=
  rfl

/-- Refining the underlying transformation recovers the original. -/
theorem NatTransCovToCovData.ofFromData_toFromData
    {dataG dataH : FunctorCovToCovData G F}
    (nat : NatTransCovToCovData G F dataG dataH) :
    NatTransCovToCovData.ofFromData nat.toFromData = nat :=
  rfl

/-- The identity transformation of the data. -/
def NatTransCovToCovData.id (data : FunctorCovToCovData G F) :
    NatTransCovToCovData G F data data :=
  NatTransCovToCovData.ofFromData (𝟙 data.toFromData)

/-- Composition of transformations of the data. -/
def NatTransCovToCovData.comp {dataG dataH dataK : FunctorCovToCovData G F}
    (nat₁ : NatTransCovToCovData G F dataG dataH)
    (nat₂ : NatTransCovToCovData G F dataH dataK) :
    NatTransCovToCovData G F dataG dataK :=
  NatTransCovToCovData.ofFromData (nat₁.toFromData ≫ nat₂.toFromData)

variable (G F)

/-- The category of data determining functors
`Grothendieck G ⥤ Grothendieck F`. -/
instance functorCovToCovDataCategory :
    Category.{max u₂ u₅ v₃ v₆} (FunctorCovToCovData G F) where
  Hom := NatTransCovToCovData G F
  id := NatTransCovToCovData.id
  comp := NatTransCovToCovData.comp
  id_comp nat := by
    unfold NatTransCovToCovData.id NatTransCovToCovData.comp
    conv_rhs => rw [← NatTransCovToCovData.ofFromData_toFromData nat]
    congr 1
    exact Category.id_comp _
  comp_id nat := by
    unfold NatTransCovToCovData.id NatTransCovToCovData.comp
    conv_rhs => rw [← NatTransCovToCovData.ofFromData_toFromData nat]
    congr 1
    exact Category.comp_id _
  assoc nat₁ nat₂ nat₃ := by
    unfold NatTransCovToCovData.comp
    congr 1
    exact Category.assoc _ _ _

/-- The forward comparison with the category of data determining functors out of
`Grothendieck G`. -/
def functorCovToCovDataToFromData : FunctorCovToCovData G F ⥤
    Grothendieck.FunctorFromData G (Grothendieck F) where
  obj := FunctorCovToCovData.toFromData
  map := NatTransCovToCovData.toFromData
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The backward comparison with the category of data determining functors out
of `Grothendieck G`. -/
def fromDataToFunctorCovToCovData :
    Grothendieck.FunctorFromData G (Grothendieck F) ⥤
      FunctorCovToCovData G F where
  obj := FunctorCovToCovData.ofFromData
  map {_ _} nat := NatTransCovToCovData.ofFromData nat
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of data determining functors `Grothendieck G ⥤ Grothendieck F`
is equivalent to the category of data determining functors out of
`Grothendieck G`, by mutually inverse comparisons. -/
def functorCovToCovDataEquivFromData : FunctorCovToCovData G F ≌
    Grothendieck.FunctorFromData G (Grothendieck F) where
  functor := functorCovToCovDataToFromData G F
  inverse := fromDataToFunctorCovToCovData G F
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.id_comp _

/-- The category of data determining functors `Grothendieck G ⥤ Grothendieck F`
is equivalent to that functor category. -/
def functorCovToCovDataEquivCat :
    FunctorCovToCovData G F ≌ (Grothendieck G ⥤ Grothendieck F) :=
  (functorCovToCovDataEquivFromData G F).trans
    (Grothendieck.functorFromDataEquivCat G (Grothendieck F))

end FunctorCovToCov

/-! #### From a covariant to a contravariant Grothendieck construction -/

section FunctorCovToContra

variable (G : B ⥤ Cat.{v₂, u₂}) (F : Pᵒᵖ ⥤ Cat.{v₃, u₃})

/-- The fibrewise component of the data determining a functor
`Grothendieck G ⥤ CoGrothendieck F`: for each object of the base, the data
determining a functor from that fiber into `CoGrothendieck F`. -/
abbrev FunctorCovToContraFib := ∀ c : B, CoGrothendieck.FunctorToData F ↑(G.obj c)

/-- The family of fiber functors determined by a fibrewise component. -/
abbrev FunctorCovToContraFibFunctor (fibTo : FunctorCovToContraFib G F) :
    Grothendieck.FunctorFromFib G (CoGrothendieck F) :=
  fun c ↦ CoGrothendieck.functorTo (fibTo c)

/-- The transition component: for each morphism of the base, the data
determining a transformation from the fiber functor at its source to the fiber
functor at its target precomposed with the pushforward. -/
abbrev FunctorCovToContraHom (fibTo : FunctorCovToContraFib G F) :=
  ∀ {c c' : B} (f : c ⟶ c'), fibTo c ⟶ (fibTo c').precomp (G.map f).toFunctor

/-- The family of transitions determined by a transition component. -/
abbrev FunctorCovToContraHomNat (fibTo : FunctorCovToContraFib G F)
    (homNat : FunctorCovToContraHom G F fibTo) :
    Grothendieck.FunctorFromHom G (FunctorCovToContraFibFunctor G F fibTo) :=
  fun f ↦ CoGrothendieck.natTransTo (homNat f)

/-- The data determining a functor `Grothendieck G ⥤ CoGrothendieck F`. -/
structure FunctorCovToContraData : Type (max u₂ v₂ u₃ v₃ u₅ v₅ u₆ v₆) where
  /-- The data determining a functor out of each fiber. -/
  fibTo : FunctorCovToContraFib G F
  /-- The data determining the transition over each morphism of the base. -/
  homNat : FunctorCovToContraHom G F fibTo
  /-- Identity coherence. -/
  homNat_id : Grothendieck.FunctorFromHomId G
    (FunctorCovToContraFibFunctor G F fibTo)
    (FunctorCovToContraHomNat G F fibTo homNat)
  /-- Composition coherence. -/
  homNat_comp : Grothendieck.FunctorFromHomComp G
    (FunctorCovToContraFibFunctor G F fibTo)
    (FunctorCovToContraHomNat G F fibTo homNat)

variable {G F}

/-- The data determining a functor out of `Grothendieck G` underlying the
data determining a functor to `CoGrothendieck F`. -/
def FunctorCovToContraData.toFromData (data : FunctorCovToContraData G F) :
    Grothendieck.FunctorFromData G (CoGrothendieck F) where
  fib := FunctorCovToContraFibFunctor G F data.fibTo
  hom := FunctorCovToContraHomNat G F data.fibTo data.homNat
  hom_id := data.homNat_id
  hom_comp := data.homNat_comp

/-- The data determining a functor to `CoGrothendieck F` underlying the data
determining a functor out of `Grothendieck G`. -/
def FunctorCovToContraData.ofFromData
    (data : Grothendieck.FunctorFromData G (CoGrothendieck F)) :
    FunctorCovToContraData G F where
  fibTo c := CoGrothendieck.ofFunctor (data.fib c)
  homNat f := CoGrothendieck.ofNatTrans (data.hom f)
  homNat_id := data.hom_id
  homNat_comp := data.hom_comp

/-- Recovering the underlying data undoes its refinement. -/
theorem FunctorCovToContraData.toFromData_ofFromData
    (data : Grothendieck.FunctorFromData G (CoGrothendieck F)) :
    (FunctorCovToContraData.ofFromData data).toFromData = data :=
  rfl

/-- Refining the underlying data recovers the original. -/
theorem FunctorCovToContraData.ofFromData_toFromData
    (data : FunctorCovToContraData G F) :
    FunctorCovToContraData.ofFromData data.toFromData = data :=
  rfl

variable (G F)

/-- The fibrewise component of a transformation of the data. -/
abbrev NatTransCovToContraFib (dataG dataH : FunctorCovToContraData G F) :=
  ∀ c : B, dataG.fibTo c ⟶ dataH.fibTo c

/-- The family of transformations determined by a fibrewise component. -/
abbrev NatTransCovToContraFibNat (dataG dataH : FunctorCovToContraData G F)
    (fibNat : NatTransCovToContraFib G F dataG dataH) :
    Grothendieck.NatTransFromFib G dataG.toFromData dataH.toFromData :=
  fun c ↦ CoGrothendieck.natTransTo (fibNat c)

/-- The data determining a transformation of functors
`Grothendieck G ⥤ CoGrothendieck F`. -/
@[ext]
structure NatTransCovToContraData (dataG dataH : FunctorCovToContraData G F) :
    Type (max u₂ u₅ v₃ v₆) where
  /-- The data determining the transformation over each fiber. -/
  fibNat : NatTransCovToContraFib G F dataG dataH
  /-- Coherence with the transition data. -/
  coherence : Grothendieck.NatTransFromCoherence G dataG.toFromData
    dataH.toFromData (NatTransCovToContraFibNat G F dataG dataH fibNat)

variable {G F}

/-- The transformation of the underlying data. -/
def NatTransCovToContraData.toFromData {dataG dataH : FunctorCovToContraData G F}
    (nat : NatTransCovToContraData G F dataG dataH) :
    dataG.toFromData ⟶ dataH.toFromData where
  fibNat := NatTransCovToContraFibNat G F dataG dataH nat.fibNat
  coherence := nat.coherence

/-- The refinement of a transformation of the underlying data. -/
def NatTransCovToContraData.ofFromData {dataG dataH : FunctorCovToContraData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    NatTransCovToContraData G F dataG dataH where
  fibNat c := CoGrothendieck.ofNatTrans (nat.fibNat c)
  coherence := nat.coherence

/-- Recovering the underlying transformation undoes its refinement. -/
theorem NatTransCovToContraData.toFromData_ofFromData
    {dataG dataH : FunctorCovToContraData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    (NatTransCovToContraData.ofFromData nat).toFromData = nat :=
  rfl

/-- Refining the underlying transformation recovers the original. -/
theorem NatTransCovToContraData.ofFromData_toFromData
    {dataG dataH : FunctorCovToContraData G F}
    (nat : NatTransCovToContraData G F dataG dataH) :
    NatTransCovToContraData.ofFromData nat.toFromData = nat :=
  rfl

/-- The identity transformation of the data. -/
def NatTransCovToContraData.id (data : FunctorCovToContraData G F) :
    NatTransCovToContraData G F data data :=
  NatTransCovToContraData.ofFromData (𝟙 data.toFromData)

/-- Composition of transformations of the data. -/
def NatTransCovToContraData.comp {dataG dataH dataK : FunctorCovToContraData G F}
    (nat₁ : NatTransCovToContraData G F dataG dataH)
    (nat₂ : NatTransCovToContraData G F dataH dataK) :
    NatTransCovToContraData G F dataG dataK :=
  NatTransCovToContraData.ofFromData (nat₁.toFromData ≫ nat₂.toFromData)

variable (G F)

/-- The category of data determining functors
`Grothendieck G ⥤ CoGrothendieck F`. -/
instance functorCovToContraDataCategory :
    Category.{max u₂ u₅ v₃ v₆} (FunctorCovToContraData G F) where
  Hom := NatTransCovToContraData G F
  id := NatTransCovToContraData.id
  comp := NatTransCovToContraData.comp
  id_comp nat := by
    unfold NatTransCovToContraData.id NatTransCovToContraData.comp
    conv_rhs => rw [← NatTransCovToContraData.ofFromData_toFromData nat]
    congr 1
    exact Category.id_comp _
  comp_id nat := by
    unfold NatTransCovToContraData.id NatTransCovToContraData.comp
    conv_rhs => rw [← NatTransCovToContraData.ofFromData_toFromData nat]
    congr 1
    exact Category.comp_id _
  assoc nat₁ nat₂ nat₃ := by
    unfold NatTransCovToContraData.comp
    congr 1
    exact Category.assoc _ _ _

/-- The forward comparison with the category of data determining functors out of
`Grothendieck G`. -/
def functorCovToContraDataToFromData : FunctorCovToContraData G F ⥤
    Grothendieck.FunctorFromData G (CoGrothendieck F) where
  obj := FunctorCovToContraData.toFromData
  map := NatTransCovToContraData.toFromData
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The backward comparison with the category of data determining functors out
of `Grothendieck G`. -/
def fromDataToFunctorCovToContraData :
    Grothendieck.FunctorFromData G (CoGrothendieck F) ⥤
      FunctorCovToContraData G F where
  obj := FunctorCovToContraData.ofFromData
  map {_ _} nat := NatTransCovToContraData.ofFromData nat
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of data determining functors `Grothendieck G ⥤ CoGrothendieck F`
is equivalent to the category of data determining functors out of
`Grothendieck G`, by mutually inverse comparisons. -/
def functorCovToContraDataEquivFromData : FunctorCovToContraData G F ≌
    Grothendieck.FunctorFromData G (CoGrothendieck F) where
  functor := functorCovToContraDataToFromData G F
  inverse := fromDataToFunctorCovToContraData G F
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.id_comp _

/-- The category of data determining functors `Grothendieck G ⥤ CoGrothendieck F`
is equivalent to that functor category. -/
def functorCovToContraDataEquivCat :
    FunctorCovToContraData G F ≌ (Grothendieck G ⥤ CoGrothendieck F) :=
  (functorCovToContraDataEquivFromData G F).trans
    (Grothendieck.functorFromDataEquivCat G (CoGrothendieck F))

end FunctorCovToContra

/-! #### From a contravariant to a covariant Grothendieck construction -/

section FunctorContraToCov

variable (G : Bᵒᵖ ⥤ Cat.{v₂, u₂}) (F : P ⥤ Cat.{v₃, u₃})

/-- The fibrewise component of the data determining a functor
`CoGrothendieck G ⥤ Grothendieck F`: for each object of the base, the data
determining a functor from that fiber into `Grothendieck F`. -/
abbrev FunctorContraToCovFib := ∀ c : B, Grothendieck.FunctorToData F ↑(G.obj (Opposite.op c))

/-- The family of fiber functors determined by a fibrewise component. -/
abbrev FunctorContraToCovFibFunctor (fibTo : FunctorContraToCovFib G F) :
    CoGrothendieck.FunctorFromFib G (Grothendieck F) :=
  fun c ↦ Grothendieck.functorTo (fibTo c)

/-- The transition component: for each morphism of the base, the data
determining a transformation from the fiber functor at its source
precomposed with the pullback to the fiber functor at its target. -/
abbrev FunctorContraToCovHom (fibTo : FunctorContraToCovFib G F) :=
  ∀ {c c' : B} (f : c ⟶ c'), (fibTo c).precomp (G.map f.op).toFunctor ⟶ fibTo c'

/-- The family of transitions determined by a transition component. -/
abbrev FunctorContraToCovHomNat (fibTo : FunctorContraToCovFib G F)
    (homNat : FunctorContraToCovHom G F fibTo) :
    CoGrothendieck.FunctorFromHom G (FunctorContraToCovFibFunctor G F fibTo) :=
  fun f ↦ Grothendieck.natTransTo (homNat f)

/-- The data determining a functor `CoGrothendieck G ⥤ Grothendieck F`. -/
structure FunctorContraToCovData : Type (max u₂ v₂ u₃ v₃ u₅ v₅ u₆ v₆) where
  /-- The data determining a functor out of each fiber. -/
  fibTo : FunctorContraToCovFib G F
  /-- The data determining the transition over each morphism of the base. -/
  homNat : FunctorContraToCovHom G F fibTo
  /-- Identity coherence. -/
  homNat_id : CoGrothendieck.FunctorFromHomId G
    (FunctorContraToCovFibFunctor G F fibTo)
    (FunctorContraToCovHomNat G F fibTo homNat)
  /-- Composition coherence. -/
  homNat_comp : CoGrothendieck.FunctorFromHomComp G
    (FunctorContraToCovFibFunctor G F fibTo)
    (FunctorContraToCovHomNat G F fibTo homNat)

variable {G F}

/-- The data determining a functor out of `CoGrothendieck G` underlying the
data determining a functor to `Grothendieck F`. -/
def FunctorContraToCovData.toFromData (data : FunctorContraToCovData G F) :
    CoGrothendieck.FunctorFromData G (Grothendieck F) :=
  CoGrothendieck.FunctorFromData.mk (FunctorContraToCovFibFunctor G F data.fibTo)
    (FunctorContraToCovHomNat G F data.fibTo data.homNat) data.homNat_id data.homNat_comp

/-- The data determining a functor to `Grothendieck F` underlying the data
determining a functor out of `CoGrothendieck G`. -/
def FunctorContraToCovData.ofFromData
    (data : CoGrothendieck.FunctorFromData G (Grothendieck F)) :
    FunctorContraToCovData G F where
  fibTo c := Grothendieck.ofFunctor (data.fib c)
  homNat f := Grothendieck.ofNatTrans (data.hom f)
  homNat_id := data.hom_id
  homNat_comp := data.hom_comp

/-- Recovering the underlying data undoes its refinement. -/
theorem FunctorContraToCovData.toFromData_ofFromData
    (data : CoGrothendieck.FunctorFromData G (Grothendieck F)) :
    (FunctorContraToCovData.ofFromData data).toFromData = data :=
  rfl

/-- Refining the underlying data recovers the original. -/
theorem FunctorContraToCovData.ofFromData_toFromData
    (data : FunctorContraToCovData G F) :
    FunctorContraToCovData.ofFromData data.toFromData = data :=
  rfl

variable (G F)

/-- The fibrewise component of a transformation of the data. -/
abbrev NatTransContraToCovFib (dataG dataH : FunctorContraToCovData G F) :=
  ∀ c : B, dataG.fibTo c ⟶ dataH.fibTo c

/-- The family of transformations determined by a fibrewise component. -/
abbrev NatTransContraToCovFibNat (dataG dataH : FunctorContraToCovData G F)
    (fibNat : NatTransContraToCovFib G F dataG dataH) :
    CoGrothendieck.NatTransFromFib G dataG.toFromData dataH.toFromData :=
  fun c ↦ Grothendieck.natTransTo (fibNat c)

/-- The data determining a transformation of functors
`CoGrothendieck G ⥤ Grothendieck F`. -/
@[ext]
structure NatTransContraToCovData (dataG dataH : FunctorContraToCovData G F) :
    Type (max u₂ u₅ v₃ v₆) where
  /-- The data determining the transformation over each fiber. -/
  fibNat : NatTransContraToCovFib G F dataG dataH
  /-- Coherence with the transition data. -/
  coherence : CoGrothendieck.NatTransFromCoherence G dataG.toFromData
    dataH.toFromData (NatTransContraToCovFibNat G F dataG dataH fibNat)

variable {G F}

/-- The transformation of the underlying data. -/
def NatTransContraToCovData.toFromData {dataG dataH : FunctorContraToCovData G F}
    (nat : NatTransContraToCovData G F dataG dataH) :
    dataG.toFromData ⟶ dataH.toFromData :=
  CoGrothendieck.natTransFromMk
    (NatTransContraToCovFibNat G F dataG dataH nat.fibNat) nat.coherence

/-- The refinement of a transformation of the underlying data. -/
def NatTransContraToCovData.ofFromData {dataG dataH : FunctorContraToCovData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    NatTransContraToCovData G F dataG dataH where
  fibNat c := Grothendieck.ofNatTrans (CoGrothendieck.natTransFromFibNat nat c)
  coherence := CoGrothendieck.natTransFromCoherence nat

/-- Recovering the underlying transformation undoes its refinement. -/
theorem NatTransContraToCovData.toFromData_ofFromData
    {dataG dataH : FunctorContraToCovData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    (NatTransContraToCovData.ofFromData nat).toFromData = nat :=
  rfl

/-- Refining the underlying transformation recovers the original. -/
theorem NatTransContraToCovData.ofFromData_toFromData
    {dataG dataH : FunctorContraToCovData G F}
    (nat : NatTransContraToCovData G F dataG dataH) :
    NatTransContraToCovData.ofFromData nat.toFromData = nat :=
  rfl

/-- The identity transformation of the data. -/
def NatTransContraToCovData.id (data : FunctorContraToCovData G F) :
    NatTransContraToCovData G F data data :=
  NatTransContraToCovData.ofFromData (𝟙 data.toFromData)

/-- Composition of transformations of the data. -/
def NatTransContraToCovData.comp {dataG dataH dataK : FunctorContraToCovData G F}
    (nat₁ : NatTransContraToCovData G F dataG dataH)
    (nat₂ : NatTransContraToCovData G F dataH dataK) :
    NatTransContraToCovData G F dataG dataK :=
  NatTransContraToCovData.ofFromData (nat₁.toFromData ≫ nat₂.toFromData)

variable (G F)

/-- The category of data determining functors
`CoGrothendieck G ⥤ Grothendieck F`. -/
instance functorContraToCovDataCategory :
    Category.{max u₂ u₅ v₃ v₆} (FunctorContraToCovData G F) where
  Hom := NatTransContraToCovData G F
  id := NatTransContraToCovData.id
  comp := NatTransContraToCovData.comp
  id_comp nat := by
    unfold NatTransContraToCovData.id NatTransContraToCovData.comp
    conv_rhs => rw [← NatTransContraToCovData.ofFromData_toFromData nat]
    congr 1
    exact Category.id_comp _
  comp_id nat := by
    unfold NatTransContraToCovData.id NatTransContraToCovData.comp
    conv_rhs => rw [← NatTransContraToCovData.ofFromData_toFromData nat]
    congr 1
    exact Category.comp_id _
  assoc nat₁ nat₂ nat₃ := by
    unfold NatTransContraToCovData.comp
    congr 1
    exact Category.assoc _ _ _

/-- The forward comparison with the category of data determining functors out of
`CoGrothendieck G`. -/
def functorContraToCovDataToFromData : FunctorContraToCovData G F ⥤
    CoGrothendieck.FunctorFromData G (Grothendieck F) where
  obj := FunctorContraToCovData.toFromData
  map := NatTransContraToCovData.toFromData
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The backward comparison with the category of data determining functors out
of `CoGrothendieck G`. -/
def fromDataToFunctorContraToCovData :
    CoGrothendieck.FunctorFromData G (Grothendieck F) ⥤
      FunctorContraToCovData G F where
  obj := FunctorContraToCovData.ofFromData
  map {_ _} nat := NatTransContraToCovData.ofFromData nat
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of data determining functors `CoGrothendieck G ⥤ Grothendieck F`
is equivalent to the category of data determining functors out of
`CoGrothendieck G`, by mutually inverse comparisons. -/
def functorContraToCovDataEquivFromData : FunctorContraToCovData G F ≌
    CoGrothendieck.FunctorFromData G (Grothendieck F) where
  functor := functorContraToCovDataToFromData G F
  inverse := fromDataToFunctorContraToCovData G F
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.id_comp _

/-- The category of data determining functors `CoGrothendieck G ⥤ Grothendieck F`
is equivalent to that functor category. -/
def functorContraToCovDataEquivCat :
    FunctorContraToCovData G F ≌ (CoGrothendieck G ⥤ Grothendieck F) :=
  (functorContraToCovDataEquivFromData G F).trans
    (CoGrothendieck.functorFromDataEquivCat G (Grothendieck F))

end FunctorContraToCov

/-! #### From a contravariant to a contravariant Grothendieck construction -/

section FunctorContraToContra

variable (G : Bᵒᵖ ⥤ Cat.{v₂, u₂}) (F : Pᵒᵖ ⥤ Cat.{v₃, u₃})

/-- The fibrewise component of the data determining a functor
`CoGrothendieck G ⥤ CoGrothendieck F`: for each object of the base, the data
determining a functor from that fiber into `CoGrothendieck F`. -/
abbrev FunctorContraToContraFib := ∀ c : B, CoGrothendieck.FunctorToData F ↑(G.obj (Opposite.op c))

/-- The family of fiber functors determined by a fibrewise component. -/
abbrev FunctorContraToContraFibFunctor (fibTo : FunctorContraToContraFib G F) :
    CoGrothendieck.FunctorFromFib G (CoGrothendieck F) :=
  fun c ↦ CoGrothendieck.functorTo (fibTo c)

/-- The transition component: for each morphism of the base, the data
determining a transformation from the fiber functor at its source
precomposed with the pullback to the fiber functor at its target. -/
abbrev FunctorContraToContraHom (fibTo : FunctorContraToContraFib G F) :=
  ∀ {c c' : B} (f : c ⟶ c'), (fibTo c).precomp (G.map f.op).toFunctor ⟶ fibTo c'

/-- The family of transitions determined by a transition component. -/
abbrev FunctorContraToContraHomNat (fibTo : FunctorContraToContraFib G F)
    (homNat : FunctorContraToContraHom G F fibTo) :
    CoGrothendieck.FunctorFromHom G (FunctorContraToContraFibFunctor G F fibTo) :=
  fun f ↦ CoGrothendieck.natTransTo (homNat f)

/-- The data determining a functor `CoGrothendieck G ⥤ CoGrothendieck F`. -/
structure FunctorContraToContraData : Type (max u₂ v₂ u₃ v₃ u₅ v₅ u₆ v₆) where
  /-- The data determining a functor out of each fiber. -/
  fibTo : FunctorContraToContraFib G F
  /-- The data determining the transition over each morphism of the base. -/
  homNat : FunctorContraToContraHom G F fibTo
  /-- Identity coherence. -/
  homNat_id : CoGrothendieck.FunctorFromHomId G
    (FunctorContraToContraFibFunctor G F fibTo)
    (FunctorContraToContraHomNat G F fibTo homNat)
  /-- Composition coherence. -/
  homNat_comp : CoGrothendieck.FunctorFromHomComp G
    (FunctorContraToContraFibFunctor G F fibTo)
    (FunctorContraToContraHomNat G F fibTo homNat)

variable {G F}

/-- The data determining a functor out of `CoGrothendieck G` underlying the
data determining a functor to `CoGrothendieck F`. -/
def FunctorContraToContraData.toFromData (data : FunctorContraToContraData G F) :
    CoGrothendieck.FunctorFromData G (CoGrothendieck F) :=
  CoGrothendieck.FunctorFromData.mk (FunctorContraToContraFibFunctor G F data.fibTo)
    (FunctorContraToContraHomNat G F data.fibTo data.homNat) data.homNat_id data.homNat_comp

/-- The data determining a functor to `CoGrothendieck F` underlying the data
determining a functor out of `CoGrothendieck G`. -/
def FunctorContraToContraData.ofFromData
    (data : CoGrothendieck.FunctorFromData G (CoGrothendieck F)) :
    FunctorContraToContraData G F where
  fibTo c := CoGrothendieck.ofFunctor (data.fib c)
  homNat f := CoGrothendieck.ofNatTrans (data.hom f)
  homNat_id := data.hom_id
  homNat_comp := data.hom_comp

/-- Recovering the underlying data undoes its refinement. -/
theorem FunctorContraToContraData.toFromData_ofFromData
    (data : CoGrothendieck.FunctorFromData G (CoGrothendieck F)) :
    (FunctorContraToContraData.ofFromData data).toFromData = data :=
  rfl

/-- Refining the underlying data recovers the original. -/
theorem FunctorContraToContraData.ofFromData_toFromData
    (data : FunctorContraToContraData G F) :
    FunctorContraToContraData.ofFromData data.toFromData = data :=
  rfl

variable (G F)

/-- The fibrewise component of a transformation of the data. -/
abbrev NatTransContraToContraFib (dataG dataH : FunctorContraToContraData G F) :=
  ∀ c : B, dataG.fibTo c ⟶ dataH.fibTo c

/-- The family of transformations determined by a fibrewise component. -/
abbrev NatTransContraToContraFibNat (dataG dataH : FunctorContraToContraData G F)
    (fibNat : NatTransContraToContraFib G F dataG dataH) :
    CoGrothendieck.NatTransFromFib G dataG.toFromData dataH.toFromData :=
  fun c ↦ CoGrothendieck.natTransTo (fibNat c)

/-- The data determining a transformation of functors
`CoGrothendieck G ⥤ CoGrothendieck F`. -/
@[ext]
structure NatTransContraToContraData (dataG dataH : FunctorContraToContraData G F) :
    Type (max u₂ u₅ v₃ v₆) where
  /-- The data determining the transformation over each fiber. -/
  fibNat : NatTransContraToContraFib G F dataG dataH
  /-- Coherence with the transition data. -/
  coherence : CoGrothendieck.NatTransFromCoherence G dataG.toFromData
    dataH.toFromData (NatTransContraToContraFibNat G F dataG dataH fibNat)

variable {G F}

/-- The transformation of the underlying data. -/
def NatTransContraToContraData.toFromData {dataG dataH : FunctorContraToContraData G F}
    (nat : NatTransContraToContraData G F dataG dataH) :
    dataG.toFromData ⟶ dataH.toFromData :=
  CoGrothendieck.natTransFromMk
    (NatTransContraToContraFibNat G F dataG dataH nat.fibNat) nat.coherence

/-- The refinement of a transformation of the underlying data. -/
def NatTransContraToContraData.ofFromData {dataG dataH : FunctorContraToContraData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    NatTransContraToContraData G F dataG dataH where
  fibNat c := CoGrothendieck.ofNatTrans (CoGrothendieck.natTransFromFibNat nat c)
  coherence := CoGrothendieck.natTransFromCoherence nat

/-- Recovering the underlying transformation undoes its refinement. -/
theorem NatTransContraToContraData.toFromData_ofFromData
    {dataG dataH : FunctorContraToContraData G F}
    (nat : dataG.toFromData ⟶ dataH.toFromData) :
    (NatTransContraToContraData.ofFromData nat).toFromData = nat :=
  rfl

/-- Refining the underlying transformation recovers the original. -/
theorem NatTransContraToContraData.ofFromData_toFromData
    {dataG dataH : FunctorContraToContraData G F}
    (nat : NatTransContraToContraData G F dataG dataH) :
    NatTransContraToContraData.ofFromData nat.toFromData = nat :=
  rfl

/-- The identity transformation of the data. -/
def NatTransContraToContraData.id (data : FunctorContraToContraData G F) :
    NatTransContraToContraData G F data data :=
  NatTransContraToContraData.ofFromData (𝟙 data.toFromData)

/-- Composition of transformations of the data. -/
def NatTransContraToContraData.comp {dataG dataH dataK : FunctorContraToContraData G F}
    (nat₁ : NatTransContraToContraData G F dataG dataH)
    (nat₂ : NatTransContraToContraData G F dataH dataK) :
    NatTransContraToContraData G F dataG dataK :=
  NatTransContraToContraData.ofFromData (nat₁.toFromData ≫ nat₂.toFromData)

variable (G F)

/-- The category of data determining functors
`CoGrothendieck G ⥤ CoGrothendieck F`. -/
instance functorContraToContraDataCategory :
    Category.{max u₂ u₅ v₃ v₆} (FunctorContraToContraData G F) where
  Hom := NatTransContraToContraData G F
  id := NatTransContraToContraData.id
  comp := NatTransContraToContraData.comp
  id_comp nat := by
    unfold NatTransContraToContraData.id NatTransContraToContraData.comp
    conv_rhs => rw [← NatTransContraToContraData.ofFromData_toFromData nat]
    congr 1
    exact Category.id_comp _
  comp_id nat := by
    unfold NatTransContraToContraData.id NatTransContraToContraData.comp
    conv_rhs => rw [← NatTransContraToContraData.ofFromData_toFromData nat]
    congr 1
    exact Category.comp_id _
  assoc nat₁ nat₂ nat₃ := by
    unfold NatTransContraToContraData.comp
    congr 1
    exact Category.assoc _ _ _

/-- The forward comparison with the category of data determining functors out of
`CoGrothendieck G`. -/
def functorContraToContraDataToFromData : FunctorContraToContraData G F ⥤
    CoGrothendieck.FunctorFromData G (CoGrothendieck F) where
  obj := FunctorContraToContraData.toFromData
  map := NatTransContraToContraData.toFromData
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The backward comparison with the category of data determining functors out
of `CoGrothendieck G`. -/
def fromDataToFunctorContraToContraData :
    CoGrothendieck.FunctorFromData G (CoGrothendieck F) ⥤
      FunctorContraToContraData G F where
  obj := FunctorContraToContraData.ofFromData
  map {_ _} nat := NatTransContraToContraData.ofFromData nat
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of data determining functors `CoGrothendieck G ⥤ CoGrothendieck F`
is equivalent to the category of data determining functors out of
`CoGrothendieck G`, by mutually inverse comparisons. -/
def functorContraToContraDataEquivFromData : FunctorContraToContraData G F ≌
    CoGrothendieck.FunctorFromData G (CoGrothendieck F) where
  functor := functorContraToContraDataToFromData G F
  inverse := fromDataToFunctorContraToContraData G F
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.id_comp _

/-- The category of data determining functors `CoGrothendieck G ⥤ CoGrothendieck F`
is equivalent to that functor category. -/
def functorContraToContraDataEquivCat :
    FunctorContraToContraData G F ≌ (CoGrothendieck G ⥤ CoGrothendieck F) :=
  (functorContraToContraDataEquivFromData G F).trans
    (CoGrothendieck.functorFromDataEquivCat G (CoGrothendieck F))

end FunctorContraToContra

end Between

end CategoryTheory
