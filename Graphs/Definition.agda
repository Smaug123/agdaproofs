{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions.Definition
open import Setoids.Setoids
open import Setoids.Subset

module Graphs.Definition where

record Graph {a b : _} (c : _) {V' : Set a} (V : Setoid {a} {b} V') : Set (a ⊔ b ⊔ lsuc c) where
  field
    _<->_ : Rel {a} {c} V'
    noSelfRelation : (x : V') → x <-> x → False
    symmetric : {x y : V'} → x <-> y → y <-> x
    wellDefined : {x y r s : V'} → Setoid._∼_ V x y → Setoid._∼_ V r s → x <-> r → y <-> s

record GraphIso {a b c d e m : _} {V1' : Set a} {V2' : Set b} {V1 : Setoid {a} {c} V1'} {V2 : Setoid {b} {d} V2'} (G : Graph e V1) (H : Graph m V2) (f : V1' → V2') : Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ m) where
  field
    bij : SetoidBijection V1 V2 f
    respects : (x y : V1') → Graph._<->_ G x y → Graph._<->_ H (f x) (f y)
    respects' : (x y : V1') → Graph._<->_ H (f x) (f y) → Graph._<->_ G x y

record Subgraph {a b c d e : _} {V' : Set a} {V : Setoid {a} {b} V'} (G : Graph c V) {pred : V' → Set d} (sub : subset V pred) (_<->'_ : Rel {_} {e} (Sg V' pred)) : Set (a ⊔ b ⊔ c ⊔ d ⊔ e) where
  field
    inherits : {x y : Sg V' pred} → (x <->' y) → (Graph._<->_ G (underlying x) (underlying y))
    symmetric : {x y : Sg V' pred} → (x <->' y) → (y <->' x)
    wellDefined : {x y r s : Sg V' pred} → Setoid._∼_ (subsetSetoid V sub) x y → Setoid._∼_ (subsetSetoid V sub) r s → x <->' r → y <->' s

subgraphIsGraph : {a b c d e : _} {V' : Set a} {V : Setoid {a} {b} V'} {G : Graph c V} {pred : V' → Set d} {sub : subset V pred} {rel : Rel {_} {e} (Sg V' pred)} (H : Subgraph G sub rel) → Graph e (subsetSetoid V sub)
Graph._<->_ (subgraphIsGraph {rel = rel} H) = rel
Graph.noSelfRelation (subgraphIsGraph {G = G} H) (v , isSub) v=v = Graph.noSelfRelation G v (Subgraph.inherits H v=v)
Graph.symmetric (subgraphIsGraph H) v1=v2 = Subgraph.symmetric H v1=v2
Graph.wellDefined (subgraphIsGraph H) = Subgraph.wellDefined H
