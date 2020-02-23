{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Setoids.Setoids
open import Setoids.Subset
open import Graphs.Definition
open import Sets.FinSet.Definition
open import Numbers.Naturals.Semiring

module Graphs.Colouring where

Colouring : (n : ℕ) {a b c : _} {V' : Set a} {V : Setoid {a} {b} V'} (G : Graph c V) → Set (a ⊔ c)
Colouring n {V' = V'} G = {x y : V'} → (Graph._<->_ G x y) → FinSet n

inheritColouring : {n : ℕ} {a b c : _} {V' : Set a} {V : Setoid {a} {b} V'} {G : Graph c V} → (k : Colouring n G) → {e : _} {pred : V' → Set e} {sub : subset V pred} {d : _} {_<->'_ : Rel {_} {d} (Sg V' pred)} (H : Subgraph G sub _<->'_) → Colouring n (subgraphIsGraph H)
inheritColouring k H {v1 , _} {v2 , _} x-y = k (Subgraph.inherits H x-y)

Monochromatic : {a b c : Level} {V' : Set a} {V : Setoid {a} {b} V'} {G : Graph c V} {n : ℕ} → (k : Colouring n G) → {d e : _} {pred : V' → Set d} {sub : subset V pred} {_<->'_ : Rel {_} {e} (Sg V' pred)} (H : Subgraph G sub _<->'_) → Set (a ⊔ d ⊔ e)
Monochromatic {V' = V'} {n = n} k {pred = pred} {sub = sub} {_<->'_} H = Sg (FinSet n) (λ c → {x : Sg V' pred} {y : Sg V' pred} (edge : x <->' y) → (inheritColouring k H) edge ≡ c)
