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

module Rings.Ideals.Principal.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Ideals.Definition R
open Setoid S

PrincipalIdeal : {c : _} {pred : A → Set c} (ideal : Ideal pred) → Set (a ⊔ b ⊔ c)
PrincipalIdeal {pred = pred} ideal = Sg A (λ a → {x : A} → (pred x) → Sg A (λ c → (a * c) ∼ x))
