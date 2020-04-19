{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Setoids.Setoids
open import Functions.Definition
open import Rings.Definition
open import Rings.Orders.Partial.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Orders.Total.Definition {n m : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} where

open Ring R
open Group additiveGroup
open Setoid S

record TotallyOrderedRing {p : _} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} (pRing : PartiallyOrderedRing R pOrder) : Set (lsuc n ⊔ m ⊔ p) where
  field
    total : SetoidTotalOrder pOrder
  open SetoidPartialOrder pOrder
