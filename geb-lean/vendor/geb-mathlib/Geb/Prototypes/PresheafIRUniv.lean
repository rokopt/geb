/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PresheafIRUniv.Basic

/-!
# PresheafIRUniv — index

Prototype port of the Idris-2 `IRCode`/`IRdecode` example (the universe
closed under dependent sums and products) to Lean on top of the presheaf
inductive-inductive types of `Geb.Mathlib.Data.PFunctor.Presheaf.W`, with the
walking arrow as the underlying category. See `Basic` for the construction and
its relationship to the Idris-2 formulation.
-/
