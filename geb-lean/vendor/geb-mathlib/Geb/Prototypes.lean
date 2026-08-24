/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.CanonicalSExpr
public import Geb.Prototypes.Computability
public import Geb.Prototypes.ConcreteSyntax
public import Geb.Prototypes.PresheafIRProto
public import Geb.Prototypes.ReadableSExpr

/-!
# Geb.Prototypes — prototype content

Modules under this namespace are prototypes: each works out a
construction the language is to have, without its written form
being settled as the one to keep. While the expression is
provisional a module is not upstream-eligible.
They may import from `Mathlib.*`, `Batteries.*`,
`Cslib.*`, `Geb.Mathlib.*`, `Geb.Cslib.*`, `GebLang.*` or
`Geb.Prototypes.*`.
-/
