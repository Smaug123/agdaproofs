{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Sets.Cardinality.Infinite.Definition
open import Sets.Cardinality.Finite.Lemmas

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
