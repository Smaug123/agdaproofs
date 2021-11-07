{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Numbers.Naturals.Order.WellFounded
open import Orders.WellFounded.Induction
open import Orders.Total.Definition
open import Semirings.Definition

module Numbers.Naturals.Division where

open import Numbers.Naturals.EuclideanAlgorithm public using (_∣_ ; zeroDividesNothing ; divisionAlgResult ; divides ; biggerThanCantDivide ; aDivA ; aDivZero ; divEquality ; oneDivN ; dividesBothImpliesDividesSum ; dividesBothImpliesDividesDifference)

divOneImpliesOne : {a : ℕ} → a ∣ 1 → a ≡ 1
divOneImpliesOne {zero} a|1 = exFalso (zeroDividesNothing _ a|1)
divOneImpliesOne {succ zero} a|1 = refl
divOneImpliesOne {succ (succ a)} (divides record { quot = zero ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite Semiring.sumZeroRight ℕSemiring (a *N zero) | multiplicationNIsCommutative a 0 = exFalso (naughtE pr)
divOneImpliesOne {succ (succ a)} (divides record { quot = (succ quot) ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite Semiring.commutative ℕSemiring quot (succ (quot +N a *N succ quot)) = exFalso (naughtE (equalityCommutative (succInjective pr)))
