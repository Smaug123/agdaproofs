{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Setoids.Setoids
open import Setoids.Subset
open import Graphs.Definition
open import Sets.FinSet.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.EquivalenceRelations
open import Graphs.CompleteGraph
open import Graphs.Colouring

module Graphs.RamseyTriangle where

hasMonochromaticTriangle : {a : _} {n : ℕ} (G : Graph a (reflSetoid (FinSet n))) → Set (lsuc lzero)
hasMonochromaticTriangle {n = n} G = Sg (FinSet n → Set) λ pred → (subset (reflSetoid (FinSet n)) pred) && {!!}

ramseyForTriangle : (k : ℕ) → Sg ℕ (λ N → (n : ℕ) → (N <N n) → (c : Colouring k (Kn n)) → {!!})
ramseyForTriangle k = {!!}

