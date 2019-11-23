{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Sets.EquivalenceRelations
open import Rings.Ideals.Definition
open import Rings.IntegralDomains.Definition
open import Rings.Ideals.Prime.Definition
open import Rings.Cosets

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

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
