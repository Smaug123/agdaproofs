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
open import Rings.IntegralDomains.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Irreducibles.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open Setoid S
open Ring R
open import Rings.Units.Definition R

record Irreducible (r : A) : Set (a ⊔ b) where
  field
    nonzero : (r ∼ 0R) → False
    nonunit : (Unit r) → False
    irreducible : (x y : A) → (x * y) ∼ r → (Unit x → False) → Unit y
