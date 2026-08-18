/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto.Bound
public import Geb.Internal.Computability.CobhamFoldProto.Fold
public import Geb.Internal.Computability.CobhamFoldProto.SelfDelim
public import Geb.Internal.Computability.CobhamFoldProto.Layout
public import Geb.Internal.Computability.CobhamFoldProto.Expr
public import Geb.Internal.Computability.CobhamFoldProto.Variable
public import Geb.Internal.Computability.CobhamFoldProto.SmashFree
public import Geb.Internal.Computability.CobhamFoldProto.Degenerate
public import Geb.Internal.Computability.CobhamFoldProto.Initial
public import Geb.Internal.Computability.CobhamFoldProto.Destruct

/-!
# The fold over recognized terms

Index for the prototype generalizing the ranked-tree recognizer of
`Geb/Mathlib/Computability/Cobham/RankedTree.lean` to a fold at an arbitrary
algebra of the ranked alphabet.
-/
