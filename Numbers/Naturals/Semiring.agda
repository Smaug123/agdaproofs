{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import WellFoundedInduction
open import Functions
open import Orders
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Addition
open import Numbers.Naturals.Multiplication
open import Semirings.Definition
open import Monoids.Definition

module Numbers.Naturals.Semiring where

open Numbers.Naturals.Definition using (ℕ ; zero ; succ ; succInjective ; naughtE) public
open Numbers.Naturals.Addition using (_+N_ ; canSubtractFromEqualityRight ; canSubtractFromEqualityLeft) public
open Numbers.Naturals.Multiplication using (_*N_ ; multiplicationNIsCommutative) public

ℕSemiring : Semiring 0 1 _+N_ _*N_
Monoid.associative (Semiring.monoid ℕSemiring) a b c = equalityCommutative (additionNIsAssociative a b c)
Monoid.idLeft (Semiring.monoid ℕSemiring) _ = refl
Monoid.idRight (Semiring.monoid ℕSemiring) a = additionNIsCommutative a 0
Semiring.commutative ℕSemiring = additionNIsCommutative
Monoid.associative (Semiring.multMonoid ℕSemiring) = multiplicationNIsAssociative
Monoid.idLeft (Semiring.multMonoid ℕSemiring) a = additionNIsCommutative a 0
Monoid.idRight (Semiring.multMonoid ℕSemiring) a = transitivity (multiplicationNIsCommutative a 1) (additionNIsCommutative a 0)
Semiring.productZeroLeft ℕSemiring _ = refl
Semiring.productZeroRight ℕSemiring a = multiplicationNIsCommutative a 0
Semiring.+DistributesOver* ℕSemiring = productDistributes
Semiring.+DistributesOver*' ℕSemiring a b c rewrite multiplicationNIsCommutative (a +N b) c | multiplicationNIsCommutative a c | multiplicationNIsCommutative b c = productDistributes c a b

succExtracts : (x y : ℕ) → (x +N succ y) ≡ (succ (x +N y))
succExtracts x y = transitivity (Semiring.commutative ℕSemiring x (succ y)) (applyEquality succ (Semiring.commutative ℕSemiring y x))

productZeroImpliesOperandZero : {a b : ℕ} → a *N b ≡ 0 → (a ≡ 0) || (b ≡ 0)
productZeroImpliesOperandZero {zero} {b} pr = inl refl
productZeroImpliesOperandZero {succ a} {zero} pr = inr refl
productZeroImpliesOperandZero {succ a} {succ b} ()
