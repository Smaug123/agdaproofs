{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Lemmas
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Setoids
open import Functions
open import Rings.Definition
open import Rings.Lemmas
open import Sets.EquivalenceRelations
open import Fields.Fields
open import Rings.IntegralDomains.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Primes.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Divisible.Definition R
open import Rings.IntegralDomains.Lemmas intDom
open import Rings.Ideals.Definition R
open import Rings.Primes.Definition intDom
open import Rings.Ideals.Prime.Definition {R = R}
open import Rings.Irreducibles.Definition intDom
open Ring R
open Setoid S
open Equivalence eq

primeImpliesPrimeIdeal : {a : A} → Prime a → PrimeIdeal (generatedIdeal a)
primeImpliesPrimeIdeal {a} record { isPrime = isPrime ; nonzero = nonzero ; nonunit = nonunit } = record { isPrime = λ {r} {s} → isPrime r s ; notContained = 1R ; notContainedIsNotContained = bad }
  where
    bad : a ∣ 1R → False
    bad (c , ac=1) = nonunit (c , ac=1)

primeIdealImpliesPrime : {a : A} → ((a ∼ 0R) → False) → PrimeIdeal (generatedIdeal a) → Prime a
Prime.isPrime (primeIdealImpliesPrime {a} a!=0 record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) r s a|rs aNot|r = isPrime a|rs aNot|r
Prime.nonzero (primeIdealImpliesPrime {a} a!=0 record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) = a!=0
Prime.nonunit (primeIdealImpliesPrime {a} a!=0 record { isPrime = isPrime ; notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained }) (c , ac=1) = notContainedIsNotContained ((c * notContained) , transitive *Associative (transitive (*WellDefined ac=1 reflexive) identIsIdent))

primeIsIrreducible : {a : A} → Prime a → Irreducible a
Irreducible.nonzero (primeIsIrreducible {a} prime) = Prime.nonzero prime
Irreducible.nonunit (primeIsIrreducible {a} prime) = Prime.nonunit prime
Irreducible.irreducible (primeIsIrreducible {a} prime) x y xy=a xNonunit = underlying pr , yUnit
  where
    a|xy : a ∣ (x * y)
    a|xy = 1R , transitive *Commutative (transitive identIsIdent (symmetric xy=a))
    a|yFalse : (a ∣ y) → False
    a|yFalse (c , ac=y) = xNonunit (c , transitive *Commutative t)
      where
        s : (a * (c * x)) ∼ a
        s = transitive *Associative (transitive (*WellDefined ac=y reflexive) (transitive *Commutative xy=a))
        t : (c * x) ∼ 1R
        t = cancelIntDom {a} {c * x} {1R} (transitive s (symmetric (transitive *Commutative identIsIdent))) (Prime.nonzero prime)
    pr : Sg A (λ c → (a * c) ∼ x)
    pr = Prime.isPrime prime y x (divisibleWellDefined reflexive *Commutative a|xy) a|yFalse
    yUnit : (y * underlying pr) ∼ 1R
    yUnit with pr
    ... | c , ac=x = transitive *Commutative (cancelIntDom {a} {c * y} {1R} (transitive *Associative (transitive (*WellDefined ac=x reflexive) (transitive xy=a (symmetric (transitive *Commutative identIsIdent))))) (Prime.nonzero prime))
