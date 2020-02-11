{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids

module Setoids.Algebra.Lemmas {a b : _} {A : Set a} (S : Setoid {a} {b} A) where

open Setoid S
open Equivalence eq
open import Setoids.Subset S
open import Setoids.Equality S
open import Setoids.Intersection.Definition S
open import Setoids.Union.Definition S

intersectionAndUnion : {c d e : _} {pred1 : A → Set c} {pred2 : A → Set d} {pred3 : A → Set e} → (s1 : subset pred1) (s2 : subset pred2) (s3 : subset pred3) → intersection s1 (union s2 s3) =S union (intersection s1 s2) (intersection s1 s3)
intersectionAndUnion s1 s2 s3 x = ans1 ,, ans2
  where
    ans1 : _
    ans1 (fst ,, inl x) = inl (fst ,, x)
    ans1 (fst ,, inr x) = inr (fst ,, x)
    ans2 : _
    ans2 (inl x) = _&&_.fst x ,, inl (_&&_.snd x)
    ans2 (inr x) = _&&_.fst x ,, inr (_&&_.snd x)
