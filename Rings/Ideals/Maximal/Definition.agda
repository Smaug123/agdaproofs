{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Sets.EquivalenceRelations
open import Rings.Ideals.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Maximal.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {pred : A → Set c} (i : Ideal R pred) where

record MaximalIdeal {d : _} : Set (a ⊔ b ⊔ c ⊔ lsuc d) where
  field
    notContained : A
    notContainedIsNotContained : (pred notContained) → False
    isMaximal : {bigger : A → Set d} → Ideal R bigger → ({a : A} → pred a → bigger a) → (Sg A (λ a → bigger a && (pred a → False))) → ({a : A} → bigger a)
