{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions.Definition
open import Numbers.Naturals.Definition
open import Sets.FinSet.Definition

module Sets.Cardinality.Finite.Definition where

record FiniteSet {a : _} (A : Set a) : Set a where
  field
    size : ℕ
    mapping : FinSet size → A
    bij : Bijection mapping

