{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Sets.EquivalenceRelations
open import Rings.Ideals.Definition
open import Rings.IntegralDomains.Definition
open import Rings.Ideals.Prime.Definition
open import Rings.Cosets


module Rings.Ideals.Prime.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {pred : A → Set c} (i : Ideal R pred) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open import Rings.Ideals.Lemmas R

idealPrimeImpliesQuotientIntDom : PrimeIdeal i → IntegralDomain (cosetRing R i)
IntegralDomain.intDom (idealPrimeImpliesQuotientIntDom isPrime) {a} {b} ab=0 a!=0 = ans
  where
    ab=0' : pred (a * b)
    ab=0' = translate' i ab=0
    a!=0' : (pred a) → False
    a!=0' prA = a!=0 (translate i prA)
    ans' : pred b
    ans' = PrimeIdeal.isPrime isPrime ab=0' a!=0'
    ans : pred (inverse (Ring.0R (cosetRing R i)) + b)
    ans = translate i ans'
IntegralDomain.nontrivial (idealPrimeImpliesQuotientIntDom isPrime) 1=0 = PrimeIdeal.notContainedIsNotContained isPrime u
  where
    t : pred (Ring.1R (cosetRing R i))
    t = translate' i 1=0
    u : pred (PrimeIdeal.notContained isPrime)
    u = Ideal.isSubset i identIsIdent (Ideal.accumulatesTimes i {y = PrimeIdeal.notContained isPrime} t)

quotientIntDomImpliesIdealPrime : IntegralDomain (cosetRing R i) → PrimeIdeal i
quotientIntDomImpliesIdealPrime intDom = record { isPrime = isPrime ; notContained = Ring.1R R ; notContainedIsNotContained = notCon }
  where
    abstract
      notCon : pred 1R → False
      notCon 1=0 = IntegralDomain.nontrivial intDom (translate i 1=0)
      isPrime : {a b : A} → pred (a * b) → (pred a → False) → pred b
      isPrime {a} {b} predAB !predA = translate' i (IntegralDomain.intDom intDom (translate i predAB) λ t → !predA (translate' i t))

private
  dividesZero : {a : A} → generatedIdealPred R 0R a → a ∼ 0R
  dividesZero (c , pr) = symmetric (transitive (symmetric (transitive *Commutative timesZero)) pr)

zeroIdealPrimeImpliesIntDom : PrimeIdeal (generatedIdeal R 0R) → IntegralDomain R
IntegralDomain.intDom (zeroIdealPrimeImpliesIntDom record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) {a} {b} ab=0 a!=0 with isPrime {a} {b} (1R , transitive (transitive *Commutative timesZero) (symmetric ab=0)) (λ 0|a → a!=0 (dividesZero 0|a))
... | c , 0c=b = transitive (symmetric 0c=b) (transitive *Commutative timesZero)
IntegralDomain.nontrivial (zeroIdealPrimeImpliesIntDom record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) 1=0 = notContainedIsNotContained (notContained , transitive (*WellDefined (symmetric 1=0) reflexive) identIsIdent)

intDomImpliesZeroIdealPrime : IntegralDomain R → PrimeIdeal (generatedIdeal R 0R)
PrimeIdeal.isPrime (intDomImpliesZeroIdealPrime intDom) (c , 0=ab) 0not|a with IntegralDomain.intDom intDom (transitive (symmetric 0=ab) (transitive *Commutative timesZero)) (λ a=0 → 0not|a (0R , transitive timesZero (symmetric a=0)))
... | b=0 = 0R , transitive timesZero (symmetric b=0)
PrimeIdeal.notContained (intDomImpliesZeroIdealPrime intDom) = 1R
PrimeIdeal.notContainedIsNotContained (intDomImpliesZeroIdealPrime intDom) (c , 0c=1) = IntegralDomain.nontrivial intDom (symmetric (transitive (symmetric (transitive *Commutative timesZero)) 0c=1))

primeIdealWellDefined : {c : _} {pred2 : A → Set c} (ideal2 : Ideal R pred2) → ({x : A} → pred x → pred2 x) → ({x : A} → pred2 x → pred x) → PrimeIdeal i → PrimeIdeal ideal2
PrimeIdeal.isPrime (primeIdealWellDefined ideal2 predToPred2 pred2ToPred record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) p2ab notP2a = predToPred2 (isPrime (pred2ToPred p2ab) λ p → notP2a (predToPred2 p))
PrimeIdeal.notContained (primeIdealWellDefined ideal2 predToPred2 pred2ToPred record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) = notContained
PrimeIdeal.notContainedIsNotContained (primeIdealWellDefined ideal2 predToPred2 pred2ToPred record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) pred2Not = notContainedIsNotContained (pred2ToPred pred2Not)
