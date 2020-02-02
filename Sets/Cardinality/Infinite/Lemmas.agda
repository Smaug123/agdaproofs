{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Sets.Cardinality.Infinite.Definition
open import Sets.FinSet.Definition

module Sets.Cardinality.Infinite.Lemmas where

finsetNotInfinite : {n : ℕ} → InfiniteSet (FinSet n) → False
finsetNotInfinite {n} isInfinite = isInfinite n id idIsBijective

injectionInfiniteImpliesInfinite : {a b : _} {A : Set a} {B : Set b} → (isInfinite : InfiniteSet A) → {f : A → B} → Injection f → InfiniteSet B
injectionInfiniteImpliesInfinite infinite {f} inj n finiteBij isBij with bijectionImpliesInvertible isBij
injectionInfiniteImpliesInfinite {A = A} infinite {f} inj n finiteBij isBij | record { inverse = inverse ; isLeft = isLeft ; isRight = isRight } = infinite n {!!} {!!}
  where
    t : A → FinSet n
    t x = inverse (f x)
    tInj : Injection t
    tInj {x} {y} tx=ty = inj (Bijection.inj i tx=ty)
      where
        i : Bijection inverse
        i = invertibleImpliesBijection (inverseIsInvertible (record { inverse = inverse ; isLeft = isLeft ; isRight = isRight }))
    tSurj : Surjection t
    tSurj fin with finiteBij fin
    ... | b = {!!}
