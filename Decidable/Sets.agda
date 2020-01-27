{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae

module Decidable.Sets where

record DecidableSet {a : _} (A : Set a) : Set a where
  field
    eq : (a b : A) → ((a ≡ b) || ((a ≡ b) → False))
