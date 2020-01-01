{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Sets.Cardinality.Finite.Definition
open import Semirings.Definition
open import Sets.CantorBijection.CantorBijection
open import Orders.Total.Definition

module Sets.Cardinality.Countable.Definition where

open import Semirings.Lemmas ℕSemiring

record CountablyInfiniteSet {a : _} (A : Set a) : Set a where
  field
    counting : A → ℕ
    countingIsBij : Bijection counting

data Countable {a : _} (A : Set a) : Set a where
  finite : FiniteSet A → Countable A
  infinite : CountablyInfiniteSet A → Countable A

