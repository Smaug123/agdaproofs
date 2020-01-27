{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Functions
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Homomorphisms.Definition

module Groups.Homomorphisms.Examples where

identityHom : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ : A → A → A} (G : Group S _+A_) → GroupHom G G id
GroupHom.groupHom (identityHom {S = S} G) = Equivalence.reflexive (Setoid.eq S)
GroupHom.wellDefined (identityHom G) = id
