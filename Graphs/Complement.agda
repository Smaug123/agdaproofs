{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions
open import Setoids.Setoids
open import Setoids.Subset
open import Graphs.Definition
open import Sets.EquivalenceRelations

module Graphs.Complement {a b c : _} {V' : Set a} {V : Setoid {a} {b} V'} (G : Graph c V) where

open Graph G
open Setoid V
open Equivalence eq

complement : Graph (b ⊔ c) V
Graph._<->_ complement x y = ((x <-> y) → False) && ((x ∼ y) → False)
Graph.noSelfRelation complement x (pr1 ,, pr2) = pr2 reflexive
Graph.symmetric complement (x!-y ,, x!=y) = (λ pr → x!-y (Graph.symmetric G pr)) ,, λ pr → x!=y (Equivalence.symmetric eq pr)
Graph.wellDefined complement x=y r=s (x!-r ,, x!=r) = (λ y-s → x!-r (wellDefined (Equivalence.symmetric eq x=y) (Equivalence.symmetric eq r=s) y-s)) ,, λ y=s → x!=r (transitive x=y (transitive y=s (Equivalence.symmetric eq r=s)))
