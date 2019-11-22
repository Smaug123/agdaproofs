{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Lemmas
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Orders
open import Setoids.Setoids
open import Functions
open import Rings.Definition
open import Rings.Lemmas
open import Sets.EquivalenceRelations
open import Fields.Fields
open import Rings.Ideals.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Prime.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {pred : A → Set c} (i : Ideal R pred) where

PrimeIdeal : Set (a ⊔ c)
PrimeIdeal = {a b : A} → pred (a * b) → ((pred a) → False) → pred b
