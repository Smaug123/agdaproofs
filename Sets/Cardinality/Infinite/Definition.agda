{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions.Definition
open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Sets.FinSet.Definition

module Sets.Cardinality.Infinite.Definition where

InfiniteSet : {a : _} (A : Set a) → Set a
InfiniteSet A = (n : ℕ) → (f : FinSet n → A) → (Bijection f) → False

record DedekindInfiniteSet {a : _} (A : Set a) : Set a where
  field
    inj : ℕ → A
    isInjection : Injection inj
