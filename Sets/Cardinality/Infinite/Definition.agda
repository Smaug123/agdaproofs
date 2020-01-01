{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition

module Sets.Cardinality.Infinite.Definition where

InfiniteSet : {a : _} (A : Set a) → Set a
InfiniteSet A = (n : ℕ) → (f : FinSet n → A) → (Bijection f) → False

