{-# OPTIONS --safe --warning=error --without-K #-}


open import Functions
open import Numbers.Naturals.Semiring
open import Sets.Cardinality.Finite.Definition

module Sets.Cardinality.Countable.Definition where


record CountablyInfiniteSet {a : _} (A : Set a) : Set a where
  field
    counting : A → ℕ
    countingIsBij : Bijection counting

data Countable {a : _} (A : Set a) : Set a where
  finite : FiniteSet A → Countable A
  infinite : CountablyInfiniteSet A → Countable A

