{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae

module Decidable.Sets where

DecidableSet : {a : _} (A : Set a) → Set a
DecidableSet A = (a b : A) → ((a ≡ b) || ((a ≡ b) → False))
