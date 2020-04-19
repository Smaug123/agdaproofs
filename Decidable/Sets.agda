{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae

module Decidable.Sets {a : _} (A : Set a) where

DecidableSet : Set a
DecidableSet = (a b : A) → ((a ≡ b) || ((a ≡ b) → False))
