{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
open import Rings.IntegralDomains.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Primes.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Divisible.Definition R
open Ring R
open Setoid S
open import Rings.Units.Definition R

record Prime (x : A) : Set (a ⊔ b) where
  field
    isPrime : (r s : A) → (x ∣ (r * s)) → ((x ∣ r) → False) → (x ∣ s)
    nonzero : (x ∼ 0R) → False
    nonunit : Unit x → False
