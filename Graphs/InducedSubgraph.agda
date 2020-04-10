{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Setoids.Setoids
open import Setoids.Subset
open import Graphs.Definition

module Graphs.InducedSubgraph {a b c : _} {V' : Set a} {V : Setoid {a} {b} V'} (G : Graph c V) where

open Graph G

inducedSubgraph : {d : _} {pred : V' → Set d} (sub : subset V pred) → Graph c (subsetSetoid V sub)
Graph._<->_ (inducedSubgraph sub) (x , _) (y , _) = x <-> y
Graph.noSelfRelation (inducedSubgraph sub) (x , _) x=x = noSelfRelation x x=x
Graph.symmetric (inducedSubgraph sub) {x , _} {y , _} x=y = symmetric x=y
Graph.wellDefined (inducedSubgraph sub) {x , _} {y , _} {z , _} {w , _} x=y z=w x-z = wellDefined x=y z=w x-z
