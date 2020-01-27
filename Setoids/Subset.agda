{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids

module Setoids.Subset {a b : _} {A : Set a} (S : Setoid {a} {b} A) where

open Setoid S
open Equivalence eq

subset : {c : _} (pred : A → Set c) → Set (a ⊔ b ⊔ c)
subset pred = ({x y : A} → x ∼ y → pred x → pred y)

subsetSetoid : {c : _} {pred : A → Set c} → (subs : subset pred) → Setoid (Sg A pred)
Setoid._∼_ (subsetSetoid subs) (x , predX) (y , predY) = Setoid._∼_ S x y
Equivalence.reflexive (Setoid.eq (subsetSetoid subs)) {a , b} = reflexive
Equivalence.symmetric (Setoid.eq (subsetSetoid subs)) {a , prA} {b , prB} x = symmetric x
Equivalence.transitive (Setoid.eq (subsetSetoid subs)) {a , prA} {b , prB} {c , prC} x y = transitive x y
