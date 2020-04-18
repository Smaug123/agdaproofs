{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions.Definition
open import Setoids.Setoids
open import Setoids.Subset
open import Graphs.Definition
open import Sets.FinSet.Definition
open import Numbers.Naturals.Semiring
open import Sets.EquivalenceRelations

module Graphs.CompleteGraph where

CompleteGraph : {a b : _} {V' : Set a} (V : Setoid {a} {b} V') → Graph b V
Graph._<->_ (CompleteGraph V) x y = ((Setoid._∼_ V x y) → False)
Graph.noSelfRelation (CompleteGraph V) x x!=x = x!=x (Equivalence.reflexive (Setoid.eq V))
Graph.symmetric (CompleteGraph V) x!=y y=x = x!=y ((Equivalence.symmetric (Setoid.eq V)) y=x)
Graph.wellDefined (CompleteGraph V) {x} {y} {r} {s} x=y r=s x!=r y=s = x!=r (transitive x=y (transitive y=s (symmetric r=s)))
  where
    open Setoid V
    open Equivalence eq

Kn : (n : ℕ) → Graph _ (reflSetoid (FinSet n))
Kn n = CompleteGraph (reflSetoid (FinSet n))

triangle : Graph _ (reflSetoid (FinSet 3))
triangle = Kn 3
