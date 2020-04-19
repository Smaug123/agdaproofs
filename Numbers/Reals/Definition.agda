{-# OPTIONS --warning=error --safe --guardedness --without-K #-}

open import Setoids.Orders.Partial.Definition
open import Setoids.Setoids
open import LogicalFormulae
open import Rings.Definition
open import Numbers.Rationals.Definition
open import Functions.Definition

module Numbers.Reals.Definition where

open import Fields.CauchyCompletion.Definition ℚOrdered ℚField
open import Fields.CauchyCompletion.Setoid ℚOrdered ℚField
open import Fields.CauchyCompletion.Addition ℚOrdered ℚField
open import Fields.CauchyCompletion.Multiplication ℚOrdered ℚField
open import Fields.CauchyCompletion.Ring ℚOrdered ℚField
open import Fields.CauchyCompletion.Comparison ℚOrdered ℚField

ℝ : Set
ℝ = CauchyCompletion

_+R_ : ℝ → ℝ → ℝ
_+R_ = _+C_

_*R_ : ℝ → ℝ → ℝ
_*R_ = _*C_

ℝSetoid = cauchyCompletionSetoid

_=R_ : ℝ → ℝ → Set
a =R b = Setoid._∼_ cauchyCompletionSetoid a b

ℝRing : Ring cauchyCompletionSetoid _+R_ _*R_
ℝRing = CRing

injectionR : ℚ → ℝ
injectionR = injection

injectionRInjective : Injection injectionR
injectionRInjective = CInjection'

0R : ℝ
0R = injection 0Q

_<R_ : ℝ → ℝ → Set
_<R_ = _<C_

ℝPartialOrder : SetoidPartialOrder cauchyCompletionSetoid _<C_
ℝPartialOrder = <COrder
