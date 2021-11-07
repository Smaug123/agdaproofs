{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Decidable.Sets
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Semiring

module Computability.LambdaCalculus.Definition where

open import UnorderedSet.Definition (ℕDecideEquality)

data Term : Set where
  var : (v : ℕ) → Term
  lam : (x : ℕ) → Term → Term
  apply : Term → Term → Term
