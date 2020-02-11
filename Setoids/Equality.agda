{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids

module Setoids.Equality {a b : _} {A : Set a} (S : Setoid {a} {b} A) where

open import Setoids.Subset S

_=S_ : {c d : _} {pred1 : A → Set c} {pred2 : A → Set d} (s1 : subset pred1) (s2 : subset pred2) → Set _
_=S_ {pred1 = pred1} {pred2} s1 s2 = (x : A) → (pred1 x → pred2 x) && (pred2 x → pred1 x)

setoidEqualitySymmetric : {c d : _} {pred1 : A → Set c} {pred2 : A → Set d} → (s1 : subset pred1) (s2 : subset pred2) → s1 =S s2 → s2 =S s1
setoidEqualitySymmetric s1 s2 s1=s2 x = _&&_.snd (s1=s2 x) ,, _&&_.fst (s1=s2 x)

setoidEqualityTransitive : {c d e : _} {pred1 : A → Set c} {pred2 : A → Set d} {pred3 : A → Set e} (s1 : subset pred1) (s2 : subset pred2) (s3 : subset pred3) → s1 =S s2 → s2 =S s3 → s1 =S s3
setoidEqualityTransitive s1 s2 s3 s1=s2 s2=s3 x with s1=s2 x
setoidEqualityTransitive s1 s2 s3 s1=s2 s2=s3 x | p1top2 ,, p1top2' with s2=s3 x
setoidEqualityTransitive s1 s2 s3 s1=s2 s2=s3 x | p1top2 ,, p1top2' | fst ,, snd = (λ i → fst (p1top2 i)) ,, λ i → p1top2' (snd i)

setoidEqualityReflexive : {c : _} {pred : A → Set c} (s : subset pred) → s =S s
setoidEqualityReflexive s x = (λ x → x) ,, λ x → x
