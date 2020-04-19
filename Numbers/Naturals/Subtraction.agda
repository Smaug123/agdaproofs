{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition
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
