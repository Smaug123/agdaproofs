{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Functions.Definition
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Setoids.Setoids
open import Setoids.Cardinality.Infinite.Definition
open import Sets.Cardinality.Infinite.Lemmas
open import Setoids.Subset
open import Sets.EquivalenceRelations

module Setoids.Cardinality.Infinite.Lemmas where

finsetNotInfiniteSetoid : {n : ℕ} → InfiniteSetoid (reflSetoid (FinSet n)) → False
finsetNotInfiniteSetoid {n} isInfinite = isInfinite n id (record { inj = record { wellDefined = id ; injective = id } ; surj = record { wellDefined = id ; surjective = λ {x} → x , refl } })

dedekindInfiniteImpliesInfiniteSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → DedekindInfiniteSetoid S → InfiniteSetoid S
dedekindInfiniteImpliesInfiniteSetoid S record { inj = inj ; isInjection = isInj } zero f isBij with SetoidInvertible.inverse (setoidBijectiveImpliesInvertible isBij) (inj 0)
... | ()
dedekindInfiniteImpliesInfiniteSetoid {A = A} S record { inj = inj ; isInjection = isInj } (succ n) f isBij = noInjectionNToFinite {f = t} tInjective
  where
    t : ℕ → FinSet (succ n)
    t n = SetoidInvertible.inverse (setoidBijectiveImpliesInvertible isBij) (inj n)
    tInjective : Injection t
    tInjective pr = SetoidInjection.injective isInj (SetoidInjection.injective (SetoidBijection.inj (setoidInvertibleImpliesBijective (inverseInvertible (setoidBijectiveImpliesInvertible isBij)))) pr)
