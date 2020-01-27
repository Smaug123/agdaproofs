{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Sets.Cardinality.Infinite.Definition
open import Sets.FinSet.Definition

module Sets.Cardinality.Infinite.Lemmas where

finsetNotInfinite : {n : ℕ} → InfiniteSet (FinSet n) → False
finsetNotInfinite {n} isInfinite = isInfinite n id idIsBijective
