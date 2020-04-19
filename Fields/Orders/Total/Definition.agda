{-# OPTIONS --safe --warning=error --without-K #-}

open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Setoids.Setoids
open import Setoids.Orders.Partial.Definition
open import Functions.Definition
open import Fields.Fields

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Orders.Total.Definition {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) where

open Ring R

record TotallyOrderedField {p} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} (pRing : PartiallyOrderedRing R pOrder) : Set (lsuc (m ⊔ n ⊔ p)) where
  field
    oRing : TotallyOrderedRing pRing
