{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Rings.IntegralDomains.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.EuclideanDomains.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Setoid S
open Ring R

record DivisionAlgorithmResult (norm : {a : A} → ((a ∼ 0R) → False) → ℕ) {x y : A} (x!=0 : (x ∼ 0R) → False) (y!=0 : (y ∼ 0R) → False) : Set (a ⊔ b) where
  field
    quotient : A
    rem : A
    remSmall : (rem ∼ 0R) || Sg ((rem ∼ 0R) → False) (λ rem!=0 → (norm rem!=0) <N (norm y!=0))
    divAlg : x ∼ ((quotient * y) + rem)

record EuclideanDomain : Set (a ⊔ lsuc b) where
  field
    isIntegralDomain : IntegralDomain R
    norm : {a : A} → ((a ∼ 0R) → False) → ℕ
    normSize : {a b : A} → (a!=0 : (a ∼ 0R) → False) → (b!=0 : (b ∼ 0R) → False) → (c : A) → b ∼ (a * c) → (norm a!=0) ≤N (norm b!=0)
    divisionAlg : {a b : A} → (a!=0 : (a ∼ 0R) → False) → (b!=0 : (b ∼ 0R) → False) → DivisionAlgorithmResult norm a!=0 b!=0
