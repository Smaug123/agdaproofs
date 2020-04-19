{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Functions.Definition
open import Functions.Lemmas
open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Sets.Cardinality.Infinite.Definition
open import Sets.Cardinality.Finite.Lemmas
open import Numbers.Reals.Definition
open import Numbers.Rationals.Definition
open import Numbers.Integers.Definition
open import Sets.Cardinality.Infinite.Lemmas
open import Setoids.Setoids

module Sets.Cardinality.Infinite.Examples where

ℕIsInfinite : InfiniteSet ℕ
ℕIsInfinite n f bij = pigeonhole (le 0 refl) badInj
  where
    inv : ℕ → FinSet n
    inv = Invertible.inverse (bijectionImpliesInvertible bij)
    invInj : Injection inv
    invInj = Bijection.inj (invertibleImpliesBijection (inverseIsInvertible (bijectionImpliesInvertible bij)))
    bumpUp : FinSet n → FinSet (succ n)
    bumpUp = intoSmaller (le 0 refl)
    bumpUpInj : Injection bumpUp
    bumpUpInj = intoSmallerInj (le 0 refl)
    nextInj : Injection (toNat {succ n})
    nextInj = finsetInjectIntoℕ {succ n}
    bad : FinSet (succ n) → FinSet n
    bad a = (inv (toNat a))
    badInj : Injection bad
    badInj = injComp nextInj invInj

ℝIsInfinite : DedekindInfiniteSet ℝ
DedekindInfiniteSet.inj ℝIsInfinite n = injectionR (injectionQ (nonneg n))
DedekindInfiniteSet.isInjection ℝIsInfinite {x} {y} pr = nonnegInjective (injectionQInjective (injectionRInjective pr))
