{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition

module Numbers.Modulo.Definition where

ℤn : (n : ℕ) → (pr : 0 <N n) → Set
ℤn n 0<n = FinSet n
