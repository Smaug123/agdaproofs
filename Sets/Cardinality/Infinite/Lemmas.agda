{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions.Definition
open import Functions.Lemmas
open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Sets.Cardinality.Infinite.Definition
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas

module Sets.Cardinality.Infinite.Lemmas where

finsetNotInfinite : {n : ℕ} → InfiniteSet (FinSet n) → False
finsetNotInfinite {n} isInfinite = isInfinite n id idIsBijective

noInjectionNToFinite : {n : ℕ} → {f : ℕ → FinSet n} → Injection f → False
noInjectionNToFinite {n} {f} inj = pigeonhole (le 0 refl) tInj
  where
    t : FinSet (succ n) → FinSet n
    t m = f (toNat m)
    tInj : Injection t
    tInj {x} {y} fx=fy = toNatInjective x y (inj fx=fy)

dedekindInfiniteImpliesInfinite : {a : _} (A : Set a) → DedekindInfiniteSet A → InfiniteSet A
dedekindInfiniteImpliesInfinite A record { inj = inj ; isInjection = isInjection } zero f x with Invertible.inverse (bijectionImpliesInvertible x) (inj 0)
... | ()
dedekindInfiniteImpliesInfinite A record { inj = inj ; isInjection = isInj } (succ n) f isBij = noInjectionNToFinite {f = t} tInjective
  where
    t : ℕ → FinSet (succ n)
    t n = Invertible.inverse (bijectionImpliesInvertible isBij) (inj n)
    tInjective : Injection t
    tInjective pr = isInj ((Bijection.inj (invertibleImpliesBijection (inverseIsInvertible (bijectionImpliesInvertible isBij)))) pr)
