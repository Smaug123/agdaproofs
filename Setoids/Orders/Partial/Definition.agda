{-# OPTIONS --safe --warning=error --without-K #-}

open import Sets.EquivalenceRelations
open import LogicalFormulae
open import Orders.Total.Definition
open import Orders.Partial.Definition
open import Setoids.Setoids
open import Functions.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Setoids.Orders.Partial.Definition where

record SetoidPartialOrder {a b c : _} {A : Set a} (S : Setoid {a} {b} A) (_<_ : Rel {a} {c} A) : Set (a ⊔ b ⊔ c) where
  open Setoid S
  field
    <WellDefined : {a b c d : A} → (a ∼ b) → (c ∼ d) → a < c → b < d
    irreflexive : {x : A} → (x < x) → False
    <Transitive : {a b c : A} → (a < b) → (b < c) → (a < c)
  _<=_ : Rel {a} {b ⊔ c} A
  a <= b = (a < b) || (a ∼ b)
  <=Transitive : {a b c : A} → (a <= b) → (b <= c) → (a <= c)
  <=Transitive (inl a<b) (inl b<c) = inl (<Transitive a<b b<c)
  <=Transitive (inl a<b) (inr b=c) = inl (<WellDefined (Equivalence.reflexive eq) b=c a<b)
  <=Transitive (inr a=b) (inl b<c) = inl (<WellDefined (Equivalence.symmetric eq a=b) (Equivalence.reflexive eq) b<c)
  <=Transitive (inr a=b) (inr b=c) = inr (Equivalence.transitive eq a=b b=c)

partialOrderToSetoidPartialOrder : {a b : _} {A : Set a} (P : PartialOrder {a} A {b}) → SetoidPartialOrder (reflSetoid A) (PartialOrder._<_ P)
SetoidPartialOrder.<WellDefined (partialOrderToSetoidPartialOrder P) a=b c=d a<c rewrite a=b | c=d = a<c
SetoidPartialOrder.irreflexive (partialOrderToSetoidPartialOrder P) = PartialOrder.irreflexive P
SetoidPartialOrder.<Transitive (partialOrderToSetoidPartialOrder P) = PartialOrder.<Transitive P
