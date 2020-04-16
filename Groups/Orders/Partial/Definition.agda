{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Setoids
open import Functions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Orders.Partial.Definition {n m : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} (G : Group S _+_) where

open Group G
open Setoid S

record PartiallyOrderedGroup {p : _} {_<_ : Rel {_} {p} A} (pOrder : SetoidPartialOrder S _<_) : Set (lsuc n ⊔ m ⊔ p) where
  field
    orderRespectsAddition : {a b : A} → (a < b) → (c : A) → (a + c) < (b + c)
