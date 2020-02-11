{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Setoids.Subset

module Setoids.Intersection.Lemmas {a b : _} {A : Set a} (S : Setoid {a} {b} A) {c d : _} {pred1 : A → Set c} {pred2 : A → Set d} (s1 : subset S pred1) (s2 : subset S pred2) where

open import Setoids.Intersection.Definition S
open import Setoids.Equality S

intersectionCommutative : intersection s1 s2 =S intersection s2 s1
intersectionCommutative i = (λ t → _&&_.snd t ,, _&&_.fst t) ,, λ t → _&&_.snd t ,, _&&_.fst t

intersectionAssociative : {e : _} {pred3 : A → Set e} (s3 : subset S pred3) → intersection (intersection s1 s2) s3 =S intersection s1 (intersection s2 s3)
intersectionAssociative s3 x = (λ pr → _&&_.fst (_&&_.fst pr) ,, (_&&_.snd (_&&_.fst pr) ,, _&&_.snd pr)) ,, λ z → (_&&_.fst z ,, _&&_.fst (_&&_.snd z)) ,, _&&_.snd (_&&_.snd z)
