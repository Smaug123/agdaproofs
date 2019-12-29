{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Addition
open import Numbers.Naturals.Order
open import Numbers.Naturals.Multiplication
open import Numbers.Naturals.Exponentiation
open import Semirings.Definition
open import Monoids.Definition
open import Maybe

module Numbers.Naturals.Subtraction where

_-N'_ : (a b : ℕ) → Maybe ℕ
zero -N' zero = yes 0
zero -N' succ b = no
succ a -N' zero = yes (succ a)
succ a -N' succ b = a -N' b

subtractZero : (a : ℕ) → a -N' 0 ≡ yes a
subtractZero zero = refl
subtractZero (succ a) = refl
