{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Setoids.Setoids
open import Setoids.Subset
open import Graphs.Definition

module Graphs.Bipartite where

Bipartite : {a b : _} {c : _} {V' : Set a} {V : Setoid {a} {b} V'} (G : Graph c V) → Set _
Bipartite {V' = V'} {V = V} G = Sg (V' → Set) (λ partition → ((x y : V') → (Setoid._∼_ V x y) → partition x → partition y) & ((x : V') → (partition x) || ((partition x) → False)) & ((x y : V') → (Graph._<->_ G x y) → (partition x) → ((partition y) → False)))
