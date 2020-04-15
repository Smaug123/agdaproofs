{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Setoids
open import Setoids.Orders.Partial.Definition
open import Functions
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Orders.Partial.Definition {n m : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open Group additiveGroup
open Setoid S
open import Groups.Orders.Partial.Definition

record PartiallyOrderedRing {p : _} {_<_ : Rel {_} {p} A} (pOrder : SetoidPartialOrder S _<_) : Set (lsuc n ⊔ m ⊔ p) where
  field
    orderRespectsAddition : {a b : A} → (a < b) → (c : A) → (a + c) < (b + c)
    orderRespectsMultiplication : {a b : A} → (0R < a) → (0R < b) → (0R < (a * b))
  open SetoidPartialOrder pOrder

toGroup : {p : _} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} → PartiallyOrderedRing pOrder → PartiallyOrderedGroup additiveGroup pOrder
PartiallyOrderedGroup.orderRespectsAddition (toGroup p) = PartiallyOrderedRing.orderRespectsAddition p
