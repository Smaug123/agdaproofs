{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Fields.Fields
open import Rings.Orders.Total.Definition
open import Rings.Orders.Total.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Definition

module Fields.Orders.LeastUpperBounds.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {c : _} {_<_ : Rel {_} {c} A} (pOrder : SetoidPartialOrder S _<_) where

UpperBound : {d : _} {pred : A → Set d} (sub : subset S pred) (x : A) → Set _
UpperBound {pred = pred} sub x = (y : A) → pred y → (y < x) || (Setoid._∼_ S y x)

record LeastUpperBound {d : _} {pred : A → Set d} (sub : subset S pred) (x : A) : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    upperBound : UpperBound sub x
    leastUpperBound : (y : A) → UpperBound sub y → (x < y) || (Setoid._∼_ S x y)
