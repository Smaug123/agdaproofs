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
open import Numbers.Naturals.Order
open import Sets.EquivalenceRelations
open import Graphs.PathGraph

module Graphs.CycleGraph where

CycleGraph : (n : ℕ) → .(2 <N n) → Graph _ (reflSetoid (FinSet n))
Graph._<->_ (CycleGraph n _) x y = ((toNat x ≡ succ (toNat y)) || (toNat y ≡ succ (toNat x))) || (((toNat x ≡ 0) && (toNat y ≡ n)) || ((toNat y ≡ 0) && (toNat x ≡ n)))
Graph.noSelfRelation (CycleGraph n _) y (inl (inl x)) = nNotSucc x
Graph.noSelfRelation (CycleGraph n _) y (inl (inr x)) = nNotSucc x
Graph.noSelfRelation (CycleGraph (succ n) _) y (inr (inl (fst ,, snd))) = naughtE (transitivity (equalityCommutative fst) snd)
Graph.noSelfRelation (CycleGraph (succ n) _) y (inr (inr (fst ,, snd))) = naughtE (transitivity (equalityCommutative fst) snd)
Graph.symmetric (CycleGraph n _) (inl (inl x)) = inl (inr x)
Graph.symmetric (CycleGraph n _) (inl (inr x)) = inl (inl x)
Graph.symmetric (CycleGraph n _) (inr (inl x)) = inr (inr x)
Graph.symmetric (CycleGraph n _) (inr (inr x)) = inr (inl x)
Graph.wellDefined (CycleGraph n _) refl refl i = i
