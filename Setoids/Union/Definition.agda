{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids

module Setoids.Union.Definition {a b : _} {A : Set a} (S : Setoid {a} {b} A) where

open Setoid S
open Equivalence eq
open import Setoids.Subset S

unionPredicate : {c d : _} {pred1 : A → Set c} {pred2 : A → Set d} (s1 : subset pred1) (s2 : subset pred2) → A → Set (c ⊔ d)
unionPredicate {pred1 = pred1} {pred2} s1 s2 a = pred1 a || pred2 a

union : {c d : _} {pred1 : A → Set c} {pred2 : A → Set d} (s1 : subset pred1) (s2 : subset pred2) → subset (unionPredicate s1 s2)
union s1 s2 {x1} {x2} x1=x2 (inl x) = inl (s1 x1=x2 x)
union s1 s2 {x1} {x2} x1=x2 (inr x) = inr (s2 x1=x2 x)
