{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Orders.Total.Definition
open import Orders.Partial.Definition
open import Setoids.Setoids
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions.Definition
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Setoids.Orders.Total.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {c : _} {_<_ : A → A → Set c} {P : SetoidPartialOrder S _<_} (T : SetoidTotalOrder P) where

open SetoidTotalOrder T
open SetoidPartialOrder P
open Setoid S
open Equivalence eq

maxInequalitiesR : {a b c : A} → (a < b) → (a < c) → (a < max b c)
maxInequalitiesR {a} {b} {c} a<b a<c with totality b c
... | inl (inl x) = a<c
... | inl (inr x) = a<b
... | inr x = a<c

minInequalitiesR : {a b c : A} → (a < b) → (a < c) → (a < min b c)
minInequalitiesR {a} {b} {c} a<b a<c with totality b c
... | inl (inl x) = a<b
... | inl (inr x) = a<c
... | inr x = a<b

maxInequalitiesL : {a b c : A} → (a < c) → (b < c) → (max a b < c)
maxInequalitiesL {a} {b} {c} a<b a<c with totality a b
... | inl (inl x) = a<c
... | inl (inr x) = a<b
... | inr x = a<c

minInequalitiesL : {a b c : A} → (a < c) → (b < c) → (min a b < c)
minInequalitiesL {a} {b} {c} a<b a<c with totality a b
... | inl (inl x) = a<b
... | inl (inr x) = a<c
... | inr x = a<b

minLessL : (a b : A) → min a b <= a
minLessL a b with totality a b
... | inl (inl x) = inr reflexive
... | inl (inr x) = inl x
... | inr x = inr reflexive

minLessR : (a b : A) → min a b <= b
minLessR a b with totality a b
... | inl (inl x) = inl x
... | inl (inr x) = inr reflexive
... | inr x = inr x

maxGreaterL : (a b : A) → a <= max a b
maxGreaterL a b with totality a b
... | inl (inl x) = inl x
... | inl (inr x) = inr reflexive
... | inr x = inr x

maxGreaterR : (a b : A) → b <= max a b
maxGreaterR a b with totality a b
... | inl (inl x) = inr reflexive
... | inl (inr x) = inl x
... | inr x = inr reflexive
