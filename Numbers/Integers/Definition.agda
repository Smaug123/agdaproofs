{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition

module Numbers.Integers.Definition where

data ℤ : Set where
  nonneg : ℕ → ℤ
  negSucc : ℕ → ℤ
