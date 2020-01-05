{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Rings.Definition
open import Rings.IntegralDomains.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.PrincipalIdealDomains.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Ideals.Principal.Definition R
open import Rings.Ideals.Definition R

PrincipalIdealDomain : {c : _} → Set (a ⊔ b ⊔ lsuc c)
PrincipalIdealDomain {c} = {pred : A → Set c} → (ideal : Ideal pred) → PrincipalIdeal ideal
