{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Sets.Cardinality.Finite.Definition
open import Groups.Definition
open import Sets.EquivalenceRelations

module Groups.FiniteGroups.Definition where

record FiniteGroup {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_·_ : A → A → A} (G : Group S _·_) {c : _} (quotientSet : Set c) : Set (a ⊔ b ⊔ c) where
  field
    toSet : SetoidToSet S quotientSet
    finite : FiniteSet quotientSet

groupOrder : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_·_ : A → A → A} {underG : Group S _·_} {c : _} {quotientSet : Set c} (G : FiniteGroup underG quotientSet) → ℕ
groupOrder record { toSet = toSet ; finite = record { size = size ; mapping = mapping ; bij = bij } } = size
