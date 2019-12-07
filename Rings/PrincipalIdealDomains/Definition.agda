{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.PrincipalIdealDomains.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Ideals.Principal.Definition R
open import Rings.Ideals.Definition R

PrincipalIdealDomain : {c : _} → Set (a ⊔ b ⊔ lsuc c)
PrincipalIdealDomain {c} = {pred : A → Set c} → (ideal : Ideal pred) → PrincipalIdeal ideal
