/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

/-!
# Prototype: what separating a proof-relevant relation costs at each former

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

A relation between two objects comes in two forms: proof-relevant, a span, whose
elements are the witnesses of relatedness; and proof-irrelevant, a subobject,
which records only that a pair is related. Separation is the reflector from the
first onto the second, taking a span to its image. This module asks whether it
commutes with the two type formers, which is what decides whether a development
may be carried out on one side and transported to the other.

The base here is the point, where a presheaf is a type, a proof-relevant
relation is a `Type`-valued relation and its separation is `Nonempty` of it.
That is the smallest instance of the ambient, so a failure here is a failure
over every base.

The dependent-sum former commutes (`sep_sigmaRel_iff`), constructively and with
no hypothesis. The dependent-product former commutes exactly when a choice
principle holds (`piSepCommutes_iff_choiceForFamilies`): the separated relation
gives a witness at each index and the separated product needs one family of
them, which is the step choice supplies. So the two formers separate the same
way they have separated at every other question on this development — the
dependent sum passes and the dependent product is where the structure is
demanded.

`ChoiceForFamilies` is the axiom of choice in the form a topos states it
internally, and `Classical.choice` implies it. Under this repository's
constructive discipline it is not available, so on this base the reflector is
not a transport for the dependent-product former. Over the walking arrow the
commutation fails with no such principle in question
(`not_arrowPiSepCommutes`), so the two sides of the reflection carry genuinely
different universes over any base whose restriction identifies two indices.

## Main definitions

* `Sep` — separation of a proof-relevant relation: its image.
* `PiRel` / `PiSep` — the dependent-product relation formed before separating,
  and the one formed after.
* `SigmaRel` — the dependent-sum relation formed before separating.
* `ChoiceForFamilies` — an inhabited family has an inhabited product.
* `PiSepCommutes` — separation commutes with the dependent-product former.
* `ArrowPsh` / `ArrowFam` — a presheaf on the walking arrow and a family over
  one, with `ArrowFam.Pointwise` and `ArrowFam.Sect` the same two constructions
  over that base.
* `ArrowPiSepCommutes` — the commutation there.

## Main statements

* `sep_sigmaRel_iff` — the dependent-sum former commutes with separation.
* `sep_piRel` — one direction of the dependent-product former's commutation,
  which needs nothing.
* `piSepCommutes_iff_choiceForFamilies` — the other direction is the choice
  principle, neither weaker nor stronger.
* `not_arrowPiSepCommutes` — over the walking arrow the commutation fails
  outright, with no choice principle in question.

## Tags

prototype, parametricity, relation, span, separation, proof relevance,
axiom of choice
-/

@[expose] public section

namespace GebProto.RelSeparation

/-! ## Relations and their separation -/

/-- Separation of a proof-relevant relation: the pairs it relates, with the
witnesses forgotten. Over the point this is the image of a span. -/
def Sep {A A' : Type} (R : A → A' → Type) (a : A) (a' : A') : Prop :=
  Nonempty (R a a')

/-- The choice principle: a family of inhabited types has an inhabited product.
This is the axiom of choice in the form a topos states it internally, weaker
than `Classical.choice`, which extracts an element rather than the assertion
that one exists. -/
def ChoiceForFamilies : Prop :=
  ∀ (X : Type) (T : X → Type), (∀ x, Nonempty (T x)) → Nonempty (∀ x, T x)

/-! ## The two formers

An index relation `R`, a family of relations `S` indexed by a related pair and a
witness of its relatedness, and the two formers applied to them. -/

variable {A A' : Type} {Y : A → Type} {Y' : A' → Type}

/-- The dependent-sum relation, proof-relevant: a witness that the indices are
related, together with a witness that the values are. -/
def SigmaRel (R : A → A' → Type) (S : ∀ a a', R a a' → Y a → Y' a' → Type)
    (p : Σ a, Y a) (p' : Σ a', Y' a') : Type :=
  Σ r : R p.1 p'.1, S p.1 p'.1 r p.2 p'.2

/-- The dependent-product relation, proof-relevant: a witness at every related
pair of indices. -/
def PiRel (R : A → A' → Type) (S : ∀ a a', R a a' → Y a → Y' a' → Type)
    (f : ∀ a, Y a) (f' : ∀ a', Y' a') : Type :=
  ∀ a a' (r : R a a'), S a a' r (f a) (f' a')

/-- The dependent-product relation formed after separating: at every related
pair of indices the values are related, with no family of witnesses asked for. -/
def PiSep (R : A → A' → Type) (S : ∀ a a', R a a' → Y a → Y' a' → Type)
    (f : ∀ a, Y a) (f' : ∀ a', Y' a') : Prop :=
  ∀ a a' (r : R a a'), Sep (S a a' r) (f a) (f' a')

/-! ## The dependent-sum former commutes -/

/-- Separating the dependent-sum relation is forming it from the separations:
the witness of relatedness of a pair is a pair of witnesses, so forgetting them
one at a time and all at once agree. -/
theorem sep_sigmaRel_iff (R : A → A' → Type) (S : ∀ a a', R a a' → Y a → Y' a' → Type)
    (p : Σ a, Y a) (p' : Σ a', Y' a') :
    Sep (SigmaRel R S) p p' ↔ ∃ r : R p.1 p'.1, Sep (S p.1 p'.1 r) p.2 p'.2 :=
  ⟨fun ⟨⟨r, s⟩⟩ ↦ ⟨r, ⟨s⟩⟩, fun ⟨r, ⟨s⟩⟩ ↦ ⟨⟨r, s⟩⟩⟩

/-! ## The dependent-product former commutes exactly when choice holds -/

/-- One direction needs nothing: a family of witnesses restricts to a witness at
each related pair. -/
theorem sep_piRel (R : A → A' → Type) (S : ∀ a a', R a a' → Y a → Y' a' → Type)
    (f : ∀ a, Y a) (f' : ∀ a', Y' a') (h : Sep (PiRel R S) f f') : PiSep R S f f' :=
  fun a a' r ↦ h.elim fun g ↦ ⟨g a a' r⟩

/-- Separation commutes with the dependent-product former: the direction that
turns a witness at each related pair into one family of them. -/
def PiSepCommutes : Prop :=
  ∀ (A A' : Type) (Y : A → Type) (Y' : A' → Type) (R : A → A' → Type)
    (S : ∀ a a', R a a' → Y a → Y' a' → Type) (f : ∀ a, Y a) (f' : ∀ a', Y' a'),
      PiSep R S f f' → Sep (PiRel R S) f f'

/-- The commutation is the choice principle. So on this base the reflector
transports the dependent-product former exactly when choice is available, and
the two sides of the reflection carry the same universe exactly then. -/
theorem piSepCommutes_iff_choiceForFamilies : PiSepCommutes ↔ ChoiceForFamilies := by
  constructor
  · intro h X T hT
    exact (h X Unit (fun _ ↦ Unit) (fun _ ↦ Unit) (fun _ _ ↦ Unit)
      (fun a _ _ _ _ ↦ T a) (fun _ ↦ ()) (fun _ ↦ ())
      (fun a _ _ ↦ hT a)).elim fun g ↦ ⟨fun x ↦ g x () ()⟩
  · intro hc A A' Y Y' R S f f' h
    exact (hc (Σ a, Σ a', R a a') (fun x ↦ S x.1 x.2.1 x.2.2 (f x.1) (f' x.2.1))
      (fun x ↦ h x.1 x.2.1 x.2.2)).elim fun g ↦ ⟨fun a a' r ↦ g ⟨a, a', r⟩⟩


/-! ## Over the walking arrow the obstruction is not the metatheory's

A presheaf on the walking arrow is two types with a restriction between them,
and a family over one is a family at each stage together with a restriction
lying over the index's. The dependent-product relation read at the arrow's
target is a section of the family — the slice there is the whole base — and its
separation is the family's inhabitation at each index and each stage. The two
part with no appeal to a choice principle: `not_arrowPiSepCommutes` refutes the
commutation outright, at two indices over one. So the failure over the point is
not an artifact of doing without choice; a base with a non-injective restriction
map produces it on its own. -/

/-- A presheaf on the walking arrow: a type at each of the two objects and the
restriction along the arrow. -/
@[ext]
structure ArrowPsh where
  /-- The value at the arrow's target. -/
  top : Type
  /-- The value at the arrow's source. -/
  bot : Type
  /-- The restriction along the arrow. -/
  res : top → bot

/-- A family of presheaves over a presheaf on the walking arrow, which is what
the witnesses of a relation over an index form. -/
structure ArrowFam (A : ArrowPsh) where
  /-- The witnesses at the arrow's target. -/
  top : A.top → Type
  /-- The witnesses at the arrow's source. -/
  bot : A.bot → Type
  /-- The restriction, lying over the index's. -/
  res : ∀ x, top x → bot (A.res x)

/-- The separated dependent-product relation: a witness at each index, at each
stage, with no compatibility asked for. -/
def ArrowFam.Pointwise {A : ArrowPsh} (B : ArrowFam A) : Prop :=
  (∀ x, Nonempty (B.top x)) ∧ (∀ b, Nonempty (B.bot b))

/-- The dependent-product relation at the arrow's target: one family of
witnesses, compatible with restriction. -/
structure ArrowFam.Sect {A : ArrowPsh} (B : ArrowFam A) where
  /-- The witness at each index at the arrow's target. -/
  top : ∀ x, B.top x
  /-- The witness at each index at the arrow's source. -/
  bot : ∀ b, B.bot b
  /-- Compatibility with restriction. -/
  res : ∀ x, B.res x (top x) = bot (A.res x)

/-- Two indices at the target restricting to one at the source, which is the
non-injective restriction the failure needs. -/
def arrowIndex : ArrowPsh where
  top := Bool
  bot := Unit
  res _ := ()

/-- One witness over each index at the target and two at the source, with the
restriction over an index landing on the witness that index names. -/
def arrowFam : ArrowFam arrowIndex where
  top _ := Unit
  bot _ := Bool
  res x _ := x

/-- The family is inhabited at each index and each stage, so the separated
dependent-product relation holds. -/
theorem arrowFam_pointwise : arrowFam.Pointwise :=
  ⟨fun _ ↦ ⟨()⟩, fun _ ↦ ⟨true⟩⟩

/-- It has no section: the two indices at the target restrict to one index at
the source, and demand different witnesses there. -/
theorem not_nonempty_arrowFam_sect : ¬ Nonempty arrowFam.Sect :=
  fun h ↦ h.elim fun s ↦ Bool.noConfusion ((s.res true).trans (s.res false).symm)

/-- Separation commutes with the dependent-product former over the walking
arrow: a family inhabited at each index and each stage has a section. -/
def ArrowPiSepCommutes : Prop :=
  ∀ (A : ArrowPsh) (B : ArrowFam A), B.Pointwise → Nonempty B.Sect

/-- It does not. Over a base whose restriction identifies two indices, the
separated dependent-product relation holds where the dependent-product relation
is empty, and no choice principle is in question. -/
theorem not_arrowPiSepCommutes : ¬ ArrowPiSepCommutes :=
  fun h ↦ not_nonempty_arrowFam_sect (h arrowIndex arrowFam arrowFam_pointwise)

end GebProto.RelSeparation
