{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Numbers.Naturals.Definition
open import Sets.FinSet.Definition
open import Setoids.Setoids

module Setoids.Cardinality.Finite.Definition where

record FiniteSetoid {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
  field
    size : ℕ
    mapping : FinSet size → A
    bij : SetoidBijection (reflSetoid (FinSet size)) S mapping

