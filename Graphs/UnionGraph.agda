{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Setoids.Setoids
open import Setoids.DirectSum
open import Setoids.Subset
open import Graphs.Definition
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.EquivalenceRelations
open import Graphs.PathGraph

module Graphs.UnionGraph where

unionGraph : {a b c d e f : _} {V' : Set a} {V : Setoid {a} {b} V'} (G : Graph c V) {W' : Set d} {W : Setoid {d} {e} W'} (H : Graph f W) → Graph (c ⊔ f) (directSumSetoid V W)
Graph._<->_ (unionGraph {c = c} {f = f} G H) (inl v) (inl v2) = embedLevel {c} {f} (Graph._<->_ G v v2)
Graph._<->_ (unionGraph G H) (inl v) (inr w) = False'
Graph._<->_ (unionGraph G H) (inr w) (inl v) = False'
Graph._<->_ (unionGraph {c = c} {f = f} G H) (inr w) (inr w2) = embedLevel {f} {c} (Graph._<->_ H w w2)
Graph.noSelfRelation (unionGraph G H) (inl v) (v=v ,, _) = Graph.noSelfRelation G v v=v
Graph.noSelfRelation (unionGraph G H) (inr w) (w=w ,, _) = Graph.noSelfRelation H w w=w
Graph.symmetric (unionGraph G H) {inl x} {inl y} (x=y ,, _) = Graph.symmetric G x=y ,, record {}
Graph.symmetric (unionGraph G H) {inr x} {inr y} (x=y ,, _) = Graph.symmetric H x=y ,, record {}
Graph.wellDefined (unionGraph G H) {inl x} {inl y} {inl z} {inl w} (x=y ,, _) (y=z ,, _) (z=w ,, _) = Graph.wellDefined G x=y y=z z=w ,, record {}
Graph.wellDefined (unionGraph G H) {inr x} {inr y} {inr z} {inr w} (x=y ,, _) (y=z ,, _) (z=w ,, _) = Graph.wellDefined H x=y y=z z=w ,, record {}
