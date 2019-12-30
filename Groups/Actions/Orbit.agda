{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Groups.Definition
open import Groups.Lemmas
open import Groups.Groups
open import Groups.Actions.Definition
open import Sets.EquivalenceRelations

module Groups.Actions.Orbit where

data Orbit {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) : Set (a ⊔ b ⊔ c ⊔ d) where
  orbitElt : (g : A) → Orbit action x

orbitSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Setoid (Orbit action x)
Setoid._∼_ (orbitSetoid {T = T} action x) (orbitElt a) (orbitElt b) = Setoid._∼_ T (GroupAction.action action a x) (GroupAction.action action b x)
Equivalence.reflexive (Setoid.eq (orbitSetoid {T = T} action x)) {orbitElt g} = Equivalence.reflexive (Setoid.eq T)
Equivalence.symmetric (Setoid.eq (orbitSetoid {T = T} action x)) {orbitElt g} {orbitElt h} = Equivalence.symmetric (Setoid.eq T)
Equivalence.transitive (Setoid.eq (orbitSetoid {T = T} action x)) {orbitElt g} {orbitElt h} {orbitElt i} = Equivalence.transitive (Setoid.eq T)
