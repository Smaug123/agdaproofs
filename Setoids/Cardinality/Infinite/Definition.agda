{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Functions.Definition
open import Numbers.Naturals.Definition
open import Sets.FinSet.Definition
open import Setoids.Setoids

module Setoids.Cardinality.Infinite.Definition where

InfiniteSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Set (a ⊔ b)
InfiniteSetoid {A = A} S = (n : ℕ) → (f : FinSet n → A) → (SetoidBijection (reflSetoid (FinSet n)) S f) → False

record DedekindInfiniteSetoid {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
  field
    inj : ℕ → A
    isInjection : SetoidInjection (reflSetoid ℕ) S inj
