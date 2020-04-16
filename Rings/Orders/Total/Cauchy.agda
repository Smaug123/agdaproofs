{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Rings.Orders.Total.Cauchy {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) where

open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.AbsoluteValue order

cauchy : Sequence A → Set (m ⊔ o)
cauchy s = ∀ (ε : A) → (Ring.0R R < ε) → Sg ℕ (λ N → ∀ {m n : ℕ} → (N <N m) → (N <N n) → abs (Ring._-R_ R (index s m) (index s n)) < ε)
