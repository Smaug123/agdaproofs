{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition

module Numbers.Integers.Definition where

data ℤ : Set where
  nonneg : ℕ → ℤ
  negSucc : ℕ → ℤ

data ℤSimple : Set where
  negativeSucc : (a : ℕ) → ℤSimple
  positiveSucc : (a : ℕ) → ℤSimple
  zZero : ℤSimple

convertZ : ℤ → ℤSimple
convertZ (nonneg zero) = zZero
convertZ (nonneg (succ x)) = positiveSucc x
convertZ (negSucc x) = negativeSucc x

convertZ' : ℤSimple → ℤ
convertZ' (negativeSucc a) = negSucc a
convertZ' (positiveSucc a) = nonneg (succ a)
convertZ' zZero = nonneg 0

zIsZ : (a : ℤ) → convertZ' (convertZ a) ≡ a
zIsZ (nonneg zero) = refl
zIsZ (nonneg (succ x)) = refl
zIsZ (negSucc x) = refl

zIsZ' : (a : ℤSimple) → convertZ (convertZ' a) ≡ a
zIsZ' (negativeSucc a) = refl
zIsZ' (positiveSucc a) = refl
zIsZ' zZero = refl
