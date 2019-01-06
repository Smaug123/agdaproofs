{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Naturals
open import Groups
open import Rings
open import Integers

module TempIntegers where

  t : {a b : ℕ} → (negSucc a *Z negSucc b) ≡ nonneg 0 → False
  t {a} {b} pr with convertZ (negSucc a)
  t {a} {b} () | negative a₁ x
  t {a} {b} () | positive a₁ x
  t {a} {b} () | zZero
