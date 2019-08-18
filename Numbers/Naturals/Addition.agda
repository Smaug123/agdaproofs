{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition

module Numbers.Naturals.Addition where

infix 15 _+N_
_+N_ : ℕ → ℕ → ℕ
zero +N y = y
succ x +N y = succ (x +N y)

addzeroLeft : (x : ℕ) → (zero +N x) ≡ x
addzeroLeft x = refl

addZeroRight : (x : ℕ) → (x +N zero) ≡ x
addZeroRight zero = refl
addZeroRight (succ x) rewrite addZeroRight x = refl

succExtracts : (x y : ℕ) → (x +N succ y) ≡ (succ (x +N y))
succExtracts zero y = refl
succExtracts (succ x) y = applyEquality succ (succExtracts x y)

succCanMove : (x y : ℕ) → (x +N succ y) ≡ (succ x +N y)
succCanMove x y = transitivity (succExtracts x y) refl

additionNIsCommutative : (x y : ℕ) → (x +N y) ≡ (y +N x)
additionNIsCommutative zero y = transitivity (addzeroLeft y) (equalityCommutative (addZeroRight y))
additionNIsCommutative (succ x) zero = transitivity (addZeroRight (succ x)) refl
additionNIsCommutative (succ x) (succ y) = transitivity refl (applyEquality succ (transitivity (succCanMove x y) (additionNIsCommutative (succ x) y)))

addingPreservesEqualityRight : {a b : ℕ} (c : ℕ) → (a ≡ b) → (a +N c ≡ b +N c)
addingPreservesEqualityRight {a} {b} c pr = applyEquality (λ n -> n +N c) pr
addingPreservesEqualityLeft : {a b : ℕ} (c : ℕ) → (a ≡ b) → (c +N a ≡ c +N b)
addingPreservesEqualityLeft {a} {b} c pr = applyEquality (λ n -> c +N n) pr

additionNIsAssociative : (a b c : ℕ) → ((a +N b) +N c) ≡ (a +N (b +N c))
additionNIsAssociative zero b c = refl
additionNIsAssociative (succ a) zero c = transitivity (transitivity (applyEquality (λ n → n +N c) (applyEquality succ (addZeroRight a))) refl) (transitivity refl refl)
additionNIsAssociative (succ a) (succ b) c = transitivity refl (transitivity refl (transitivity (applyEquality succ (additionNIsAssociative a (succ b) c)) refl))

succIsAddOne : (a : ℕ) → succ a ≡ a +N succ zero
succIsAddOne a = equalityCommutative (transitivity (additionNIsCommutative a (succ zero)) refl)
