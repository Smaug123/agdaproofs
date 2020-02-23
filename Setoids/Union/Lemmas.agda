{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Setoids.Subset

module Setoids.Union.Lemmas {a b : _} {A : Set a} (S : Setoid {a} {b} A) {c d : _} {pred1 : A → Set c} {pred2 : A → Set d} (s1 : subset S pred1) (s2 : subset S pred2) where

open import Setoids.Union.Definition S
open import Setoids.Equality S

unionCommutative : union s1 s2 =S union s2 s1
unionCommutative i = ans1 ,, ans2
  where
    ans1 : unionPredicate s1 s2 i → unionPredicate s2 s1 i
    ans1 (inl x) = inr x
    ans1 (inr x) = inl x
    ans2 : unionPredicate s2 s1 i → unionPredicate s1 s2 i
    ans2 (inl x) = inr x
    ans2 (inr x) = inl x

unionAssociative : {e : _} {pred3 : A → Set e} (s3 : subset S pred3) → union (union s1 s2) s3 =S union s1 (union s2 s3)
unionAssociative s3 x = ans1 ,, ans2
  where
    ans1 : unionPredicate (union s1 s2) s3 x → unionPredicate s1 (union s2 s3) x
    ans1 (inl (inl x)) = inl x
    ans1 (inl (inr x)) = inr (inl x)
    ans1 (inr x) = inr (inr x)
    ans2 : _
    ans2 (inl x) = inl (inl x)
    ans2 (inr (inl x)) = inl (inr x)
    ans2 (inr (inr x)) = inr x
