{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.ClassicalReals.RealField
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Sets.EquivalenceRelations
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Fields
open import Groups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Functions

module Numbers.Intervals.Definition {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {_<_ : Rel {_} {c} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} (pRing : PartiallyOrderedRing R pOrder) where

record OpenInterval : Set a where
  field
    minBound : A
    maxBound : A

isInInterval : A → OpenInterval → Set c
isInInterval a record { minBound = min ; maxBound = max } = (min < a) && (a < max)
