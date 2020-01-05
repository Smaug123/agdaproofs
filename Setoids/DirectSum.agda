{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids

module Setoids.DirectSum {m n o p : _} {A : Set m} {B : Set n} (R : Setoid {m} {o} A) (S : Setoid {n} {p} B) where

open Setoid

directSumSetoid : Setoid (A && B)
_∼_ (directSumSetoid) (a ,, b) (c ,, d) = (Setoid._∼_ R a c) && (Setoid._∼_ S b d)
Equivalence.reflexive (eq (directSumSetoid)) {(a ,, b)} = Equivalence.reflexive (Setoid.eq R) ,, Equivalence.reflexive (Setoid.eq S)
Equivalence.symmetric (eq (directSumSetoid)) {(a ,, b)} {(c ,, d)} (fst ,, snd) = Equivalence.symmetric (Setoid.eq R) fst ,, Equivalence.symmetric (Setoid.eq S) snd
Equivalence.transitive (eq (directSumSetoid)) {a ,, b} {c ,, d} {e ,, f} (fst1 ,, snd1) (fst2 ,, snd2) = Equivalence.transitive (Setoid.eq R) fst1 fst2 ,, Equivalence.transitive (Setoid.eq S) snd1 snd2

directSumLift : {r s : A} {t u : B} → (Setoid._∼_ R r s) → (Setoid._∼_ S t u) → Setoid._∼_ directSumSetoid (r ,, t) (s ,, u)
_&&_.fst (directSumLift r=s t=u) = r=s
_&&_.snd (directSumLift r=s t=u) = t=u
