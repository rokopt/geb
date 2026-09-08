/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LargeIR.Basic
public import Geb.Prototypes.LargeIR.Code
public import Geb.Prototypes.LargeIR.Morphism
public import Geb.Prototypes.LargeIR.Grothendieck
public import Geb.Prototypes.LargeIR.General
public import Geb.Prototypes.LargeIR.Binder
public import Geb.Prototypes.LargeIR.Product

/-!
# LargeIR — index

Prototype transcription of a slice polynomial functor `Type/X → Type/Y` into
a presheaf polynomial endofunctor on the walking arrow, whose presheaves are
the free coproduct completion `Fam(Type)`, and the computation of what the
endofunctor does: the base map `X → Z 0` survives as data of the value, which
is the `δ` constructor of large inductive-recursive codes rather than the
slice functor itself. See `Basic` for the construction and the comparison map
along the identity section, and `Code` for the reading of the value as the
interpretation of that `δ` code in the repository's `IndRec.IR` at index type
`Type`; `Morphism` extends the agreement to morphisms of `Fam(Type)` proper,
on which the code acts positively, and `Grothendieck` packages `Fam(Type)` as
a contravariant Grothendieck construction with the code's action as an
endofunctor of it. `General` states the general case: a presheaf polynomial
endofunctor on the walking arrow is a code exactly when it is base-cartesian,
its reindexing a bijection on level-`0` directions, and the transcription is
an instance. `Binder` states why a universe's dependent-product former is not
one: its binder quantifies over a decoding, and no walking-arrow presheaf
polynomial functor has its values. `Product` replaces the walking arrow by the
walking arrow over an index type, whose presheaves are indexed families of
arrows, on which a direction names its index exactly: there a slice polynomial
functor is recovered on the nose, its W-type included.
-/
