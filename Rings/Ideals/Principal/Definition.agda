{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Principal.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Ideals.Definition R
open import Rings.Divisible.Definition R
open Setoid S

record PrincipalIdeal {c : _} {pred : A → Set c} (ideal : Ideal pred) : Set (a ⊔ b ⊔ c) where
  field
    generator : A
    genIsInIdeal : pred generator
    genGenerates : {x : A} → pred x → generator ∣ x
