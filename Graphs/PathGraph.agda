{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Setoids.Setoids
open import Setoids.Subset
open import Graphs.Definition
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Numbers.Naturals.Semiring
open import Sets.EquivalenceRelations

module Graphs.PathGraph where

nNotSucc : {n : ℕ} → (n ≡ succ n) → False
nNotSucc {zero} ()
nNotSucc {succ n} pr = nNotSucc (succInjective pr)

PathGraph : (n : ℕ) → Graph _ (reflSetoid (FinSet (succ n)))
Graph._<->_ (PathGraph n) x y = (toNat x ≡ succ (toNat y)) || (toNat y ≡ succ (toNat x))
Graph.noSelfRelation (PathGraph n) x (inl bad) = nNotSucc bad
Graph.noSelfRelation (PathGraph n) x (inr bad) = nNotSucc bad
Graph.symmetric (PathGraph n) (inl x) = inr x
Graph.symmetric (PathGraph n) (inr x) = inl x
Graph.wellDefined (PathGraph n) refl refl i = i
