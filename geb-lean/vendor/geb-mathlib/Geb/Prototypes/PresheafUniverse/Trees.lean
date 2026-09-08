/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.W
public import Geb.Prototypes.PresheafUniverse.Basic

/-!
# Prototype: codes and terms as W-trees of the universe endofunctor

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

The constructors of the universe of
`Geb/Prototypes/PresheafUniverse/Basic.lean`, as trees of the W-type of its
endofunctor. A tree over the code object `0` is a code and a tree over the term
object `1` is a term; the presheaf restriction along the walking arrow's
non-identity morphism (`typeOf`) is the typing map, and a term tree lies in the
carrier presheaf exactly when it is hereditarily natural, which is exactly when
each of its code directions carries the type of the corresponding term
direction.

The constructors build admissible trees (`SlicePFunctor.W`), whose admissibility
fixes each child's index but not the typing constraint. `pairTerm` fills its code
directions with `typeOf` of its term directions, so a tree built from the
constructors alone satisfies the constraint; a tree built from `node` directly
need not, and the constraint is decided rather than assumed, by
`FinitePresheafPFunctor.memWBool`.

## Main definitions

* `Tree` / `treeIdx` / `node` — the admissible trees, their index, and the
  node constructor.
* `baseCode` / `sigmaCode` / `piCode` — the code constructors.
* `litTerm` / `pairTerm` — the term constructors.
* `arrowHom` / `typeOf` — the walking arrow's non-identity morphism and the
  root-restriction along it, that is, the typing map.

## Main statements

* `treeIdx_node` — a node's index is its shape's output index.
* `typeOf_litTerm` / `typeOf_pairTerm` — the typing map on the term
  constructors: a literal has the base type, and a pair has the `sigma` code of
  its components' types.

## Tags

prototype, inductive-inductive, presheaf, universe, W-type, walking arrow
-/

@[expose] public section

open CategoryTheory

namespace GebProto.PresheafUniverse

/-- The admissible slice W-trees of the universe endofunctor. Those over the
code object are the codes and those over the term object the terms, once
hereditary naturality is imposed. -/
abbrev Tree : Type := universeFunctor.toSlicePFunctor.W

/-- The index of a tree: the output index of its root shape. -/
abbrev treeIdx (z : Tree) : Fin 2 := universeFunctor.toSlicePFunctor.wIndex z

/-- A node: a shape together with a family of subtrees whose indices are the
shape's direction-input indices. -/
def node (a : Shp) (v : Dir a → Tree) (hv : ∀ b, treeIdx (v b) = rDir a b) : Tree :=
  SlicePFunctor.W.mk ⟨⟨a, v⟩,
    (universeFunctor.toSliceDomPFunctor.compatible_iff _ a v).mpr hv⟩

/-- A node's index is its shape's output index. -/
theorem treeIdx_node (a : Shp) (v : Dir a → Tree) (hv : ∀ b, treeIdx (v b) = rDir a b) :
    treeIdx (node a v hv) = qShp a :=
  rfl

/-- The code of the base type. -/
def baseCode : Tree :=
  node .base (fun d ↦ d.elim) (fun d ↦ d.elim)

/-- The `sigma` code of two codes. -/
def sigmaCode (u v : Tree) (hu : treeIdx u = 0) (hv : treeIdx v = 0) : Tree :=
  node .sigma (fun i ↦ cond i v u) (fun i ↦ by cases i <;> assumption)

/-- The `pi` code of two codes. -/
def piCode (u v : Tree) (hu : treeIdx u = 0) (hv : treeIdx v = 0) : Tree :=
  node .pi (fun i ↦ cond i v u) (fun i ↦ by cases i <;> assumption)

/-- The term of the base type at `b`. -/
def litTerm (b : Bool) : Tree :=
  node (.lit b) (fun d ↦ d.elim) (fun d ↦ d.elim)

/-- The walking arrow's non-identity morphism, from the code object to the term
object. The presheaf action along it is the typing map. -/
def arrowHom : (0 : Fin 2) ⟶ (1 : Fin 2) := homOfLE (by decide)

/-- The type of a term tree: its root-restriction along `arrowHom`. -/
def typeOf (z : Tree) (hz : treeIdx z = 1) : Tree :=
  universeFunctor.wRestrTree arrowHom z hz

/-- A type is a code. -/
theorem treeIdx_typeOf (z : Tree) (hz : treeIdx z = 1) : treeIdx (typeOf z hz) = 0 :=
  universeFunctor.wIndex_wRestrTree arrowHom z hz

/-- The pair of two terms: its two term directions carry the components and its
two code directions their types. -/
def pairTerm (x y : Tree) (hx : treeIdx x = 1) (hy : treeIdx y = 1) : Tree :=
  node .pair
    (fun d ↦ match d with
      | .tm false => x
      | .tm true => y
      | .ty false => typeOf x hx
      | .ty true => typeOf y hy)
    (fun d ↦ match d with
      | .tm false => hx
      | .tm true => hy
      | .ty false => treeIdx_typeOf x hx
      | .ty true => treeIdx_typeOf y hy)

/-- The type of a literal is the base code. -/
theorem typeOf_litTerm (b : Bool) : typeOf (litTerm b) rfl = baseCode :=
  Subtype.ext (congrArg (WType.mk Shp.base) (funext fun d ↦ d.elim))

/-- The type of a pair is the `sigma` code of its components' types: the
presheaf restriction of a `pair` node restricts the shape to `sigma` and
reindexes the two subcode directions to the pair's two code directions. -/
theorem typeOf_pairTerm (x y : Tree) (hx : treeIdx x = 1) (hy : treeIdx y = 1) :
    typeOf (pairTerm x y hx hy) rfl =
      sigmaCode (typeOf x hx) (typeOf y hy) (treeIdx_typeOf x hx) (treeIdx_typeOf y hy) := by
  apply Subtype.ext
  exact congrArg (WType.mk Shp.sigma) (funext fun i ↦ by cases i <;> rfl)

end GebProto.PresheafUniverse
