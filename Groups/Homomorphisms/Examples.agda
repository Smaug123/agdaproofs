{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Homomorphisms.Definition
open import Groups.Lemmas

module Groups.Homomorphisms.Examples where

identityHom : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ : A → A → A} (G : Group S _+A_) → GroupHom G G id
GroupHom.groupHom (identityHom {S = S} G) = Equivalence.reflexive (Setoid.eq S)
GroupHom.wellDefined (identityHom G) = id
