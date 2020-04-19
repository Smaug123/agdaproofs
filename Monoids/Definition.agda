{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae

module Monoids.Definition where

record Monoid {a : _} {A : Set a} (Zero : A) (_+_ : A → A → A) : Set a where
  field
    associative : (a b c : A) → a + (b + c) ≡ (a + b) + c
    idLeft : (a : A) → Zero + a ≡ a
    idRight : (a : A) → a + Zero ≡ a
