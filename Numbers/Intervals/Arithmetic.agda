{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.ClassicalReals.RealField
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders.Partial.Definition
open import Sets.EquivalenceRelations
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Fields
open import Groups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Functions.Definition

module Numbers.Intervals.Arithmetic {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {_<_ : Rel {_} {c} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} (pRing : PartiallyOrderedRing R pOrder) where

open import Numbers.Intervals.Definition pRing
open import Rings.Orders.Partial.Lemmas pRing
open Ring R
open Group additiveGroup
open PartiallyOrderedRing pRing
open Setoid S
open Equivalence eq
open SetoidPartialOrder pOrder

intervalSum : OpenInterval → OpenInterval → OpenInterval
intervalSum record { minBound = a ; maxBound = b } record { minBound = c ; maxBound = d } = record { minBound = a + c ; maxBound = b + d }

intervalConstantSum : OpenInterval → A → OpenInterval
intervalConstantSum record { minBound = x ; maxBound = y } a = record { minBound = x + a ; maxBound = y + a }

intervalSumContains : {a b : A} → {i j : OpenInterval} → isInInterval a i → isInInterval b j → isInInterval (a + b) (intervalSum i j)
intervalSumContains (fst1 ,, snd1) (fst2 ,, snd2) = ringAddInequalities fst1 fst2 ,, ringAddInequalities snd1 snd2

intervalConstantProduct : OpenInterval → (a : A) → (0R < a) → OpenInterval
intervalConstantProduct record { minBound = minBound ; maxBound = maxBound } a 0<a = record { minBound = minBound * a ; maxBound = maxBound * a }

intervalInverse : OpenInterval → OpenInterval
intervalInverse record { minBound = b ; maxBound = c } = record { minBound = inverse c ; maxBound = inverse b }

intervalConstantSumContains : {a : A} {i : OpenInterval} (c : A) → isInInterval a i → isInInterval (a + c) (intervalConstantSum i c)
intervalConstantSumContains c (fst ,, snd) = orderRespectsAddition fst c ,, orderRespectsAddition snd c

intervalConstantProductContains : {a : A} {i : OpenInterval} {c : A} → (0<c : 0R < c) → isInInterval a i → isInInterval (a * c) (intervalConstantProduct i c 0<c)
intervalConstantProductContains {a} {i} 0<c ai = ringCanMultiplyByPositive 0<c (_&&_.fst ai) ,, ringCanMultiplyByPositive 0<c (_&&_.snd ai)

intervalInverseContains : {a : A} {i : OpenInterval} → isInInterval a i → isInInterval (inverse a) (intervalInverse i)
intervalInverseContains (less ,, greater) = ringSwapNegatives' greater ,, ringSwapNegatives' less

intervalEquality : OpenInterval → OpenInterval → Set b
intervalEquality record { minBound = minBound1 ; maxBound = maxBound1 } record { minBound = minBound ; maxBound = maxBound } = (minBound1 ∼ minBound) && (maxBound1 ∼ maxBound)

intervalWellDefined : {a : A} {i j : OpenInterval} → intervalEquality i j → isInInterval a i → isInInterval a j
intervalWellDefined (eq1 ,, eq2) (fst ,, snd) = <WellDefined eq1 reflexive fst ,, <WellDefined reflexive eq2 snd

intervalWellDefined' : {a b : A} {i : OpenInterval} → a ∼ b → isInInterval a i → isInInterval b i
intervalWellDefined' a=b (fst ,, snd) = <WellDefined reflexive a=b fst ,, <WellDefined a=b reflexive snd

increaseBoundAbove : {a minB maxB : A} → isInInterval a record { minBound = minB ; maxBound = maxB } → {bigger : A} → maxB < bigger → isInInterval a record { minBound = minB ; maxBound = bigger }
increaseBoundAbove (fst ,, snd) m<b = fst ,, <Transitive snd m<b
