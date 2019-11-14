{-# OPTIONS --warning=error --safe --guardedness #-}

open import Setoids.Orders
open import LogicalFormulae
open import Rings.Definition
open import Numbers.Rationals.Definition

module Numbers.Reals.Definition where

open import Fields.CauchyCompletion.Definition ℚOrdered ℚField
open import Fields.CauchyCompletion.Setoid ℚOrdered ℚField ℚcharNot2
open import Fields.CauchyCompletion.Addition ℚOrdered ℚField ℚcharNot2
open import Fields.CauchyCompletion.Multiplication ℚOrdered ℚField ℚcharNot2
open import Fields.CauchyCompletion.Ring ℚOrdered ℚField ℚcharNot2
open import Fields.CauchyCompletion.Comparison ℚOrdered ℚField ℚcharNot2

ℝ : Set
ℝ = CauchyCompletion

_+R_ : ℝ → ℝ → ℝ
_+R_ = _+C_

_*R_ : ℝ → ℝ → ℝ
_*R_ = _*C_

ℝRing : Ring cauchyCompletionSetoid _+R_ _*R_
ℝRing = CRing

injectionR : ℚ → ℝ
injectionR = injection

0R : ℝ
0R = injection 0Q

_<R_ : ℝ → ℝ → Set
_<R_ = _<C_

ℝPartialOrder : SetoidPartialOrder cauchyCompletionSetoid _<C_
ℝPartialOrder = <COrder
