{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids

module Setoids.DirectSum {m n o p : _} {A : Set m} {B : Set n} (R : Setoid {m} {o} A) (S : Setoid {n} {p} B) where

directSumSetoid : Setoid {m ⊔ n} (A || B)
Setoid._∼_ directSumSetoid (inl x) (inl y) = embedLevel {o} {p} (Setoid._∼_ R x y)
Setoid._∼_ directSumSetoid (inl x) (inr y) = False'
Setoid._∼_ directSumSetoid (inr x) (inl y) = False'
Setoid._∼_ directSumSetoid (inr x) (inr y) = embedLevel {p} {o} (Setoid._∼_ S x y)
Equivalence.reflexive (Setoid.eq directSumSetoid) {inl x} = Equivalence.reflexive (Setoid.eq R) {x} ,, record {}
Equivalence.reflexive (Setoid.eq directSumSetoid) {inr x} = Equivalence.reflexive (Setoid.eq S) {x} ,, record {}
Equivalence.symmetric (Setoid.eq directSumSetoid) {inl x} {inl y} (x=y ,, _) = (Equivalence.symmetric (Setoid.eq R) x=y) ,, record {}
Equivalence.symmetric (Setoid.eq directSumSetoid) {inr x} {inr y} (x=y ,, _) = (Equivalence.symmetric (Setoid.eq S) x=y) ,, record {}
Equivalence.transitive (Setoid.eq directSumSetoid) {inl x} {inl y} {inl z} (x=y ,, _) (y=z ,, _) = Equivalence.transitive (Setoid.eq R) x=y y=z ,, record {}
Equivalence.transitive (Setoid.eq directSumSetoid) {inr x} {inr y} {inr z} (x=y ,, _) (y=z ,, _) = Equivalence.transitive (Setoid.eq S) x=y y=z ,, record {}
