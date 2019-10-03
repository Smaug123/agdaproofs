{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Addition
open import Numbers.Naturals.Multiplication
open import Numbers.Naturals.Order

module Numbers.Naturals.Exponentiation where

_^N_ : ℕ → ℕ → ℕ
a ^N zero = 1
a ^N succ b = a *N (a ^N b)

exponentiationIncreases : (a b : ℕ) → (a ≡ 0) || (a ≤N a ^N (succ b))
exponentiationIncreases zero b = inl refl
exponentiationIncreases (succ a) zero = inr (inr (applyEquality succ (transitivity (additionNIsCommutative 0 a) (multiplicationNIsCommutative 1 a))))
exponentiationIncreases (succ a) (succ b) with exponentiationIncreases (succ a) b
exponentiationIncreases (succ a) (succ b) | inr (inl x) = inr (inl (canAddToOneSideOfInequality _ x))
exponentiationIncreases (succ a) (succ b) | inr (inr x) with productOne x
exponentiationIncreases (succ 0) (succ b) | inr (inr x) | inr pr rewrite pr = inr (inr refl)
exponentiationIncreases (succ (succ a)) (succ b) | inr (inr x) | inr pr rewrite pr | productWithOneRight a = inr (inl (le (succ (a +N a *N succ (succ a))) (additionNIsCommutative _ (succ (succ a)))))
