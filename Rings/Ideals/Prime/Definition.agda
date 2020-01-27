{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Ideals.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Prime.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {pred : A → Set c} (i : Ideal R pred) where

record PrimeIdeal : Set (a ⊔ c) where
  field
    isPrime : {a b : A} → pred (a * b) → ((pred a) → False) → pred b
    notContained : A
    notContainedIsNotContained : (pred notContained) → False
