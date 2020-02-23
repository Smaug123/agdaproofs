{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids

module Setoids.Product {m n o p : _} {A : Set m} {B : Set n} (R : Setoid {m} {o} A) (S : Setoid {n} {p} B) where

open Setoid

productSetoid : Setoid (A && B)
_∼_ (productSetoid) (a ,, b) (c ,, d) = (Setoid._∼_ R a c) && (Setoid._∼_ S b d)
Equivalence.reflexive (eq (productSetoid)) {(a ,, b)} = Equivalence.reflexive (Setoid.eq R) ,, Equivalence.reflexive (Setoid.eq S)
Equivalence.symmetric (eq (productSetoid)) {(a ,, b)} {(c ,, d)} (fst ,, snd) = Equivalence.symmetric (Setoid.eq R) fst ,, Equivalence.symmetric (Setoid.eq S) snd
Equivalence.transitive (eq (productSetoid)) {a ,, b} {c ,, d} {e ,, f} (fst1 ,, snd1) (fst2 ,, snd2) = Equivalence.transitive (Setoid.eq R) fst1 fst2 ,, Equivalence.transitive (Setoid.eq S) snd1 snd2

productLift : {r s : A} {t u : B} → (Setoid._∼_ R r s) → (Setoid._∼_ S t u) → Setoid._∼_ productSetoid (r ,, t) (s ,, u)
_&&_.fst (productLift r=s t=u) = r=s
_&&_.snd (productLift r=s t=u) = t=u
