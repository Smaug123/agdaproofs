{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.Naturals.Definition
open import LogicalFormulae
open import Groups.Definition
open import Groups.Orders.Partial.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Orders.Archimedean {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {G : Group S _+_} {c : _} {_<_ : A → A → Set c} {pOrder : SetoidPartialOrder S _<_} (p : PartiallyOrderedGroup G pOrder) where

open Setoid S
open import Groups.Cyclic.Definition G

Archimedean : Set (a ⊔ c)
Archimedean = (x y : A) → Sg ℕ (λ n → y < (positiveEltPower x n))
