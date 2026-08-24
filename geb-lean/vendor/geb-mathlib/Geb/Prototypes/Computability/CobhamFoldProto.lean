/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.CobhamFoldProto.Bound
public import Geb.Prototypes.Computability.CobhamFoldProto.Fold
public import Geb.Prototypes.Computability.CobhamFoldProto.SelfDelim
public import Geb.Prototypes.Computability.CobhamFoldProto.Layout
public import Geb.Prototypes.Computability.CobhamFoldProto.Expr
public import Geb.Prototypes.Computability.CobhamFoldProto.Variable
public import Geb.Prototypes.Computability.CobhamFoldProto.SmashFree
public import Geb.Prototypes.Computability.CobhamFoldProto.Degenerate
public import Geb.Prototypes.Computability.CobhamFoldProto.Initial
public import Geb.Prototypes.Computability.CobhamFoldProto.Destruct

/-!
# The fold over recognized terms

Index for the prototype generalizing the ranked-tree recognizer of
`Geb/Mathlib/Computability/Cobham/RankedTree.lean` to a fold at an arbitrary
algebra of the ranked alphabet.
-/
