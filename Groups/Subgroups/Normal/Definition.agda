{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Groups
open import Groups.Definition
open import Orders
open import Numbers.Integers.Integers
open import Setoids.Setoids
open import LogicalFormulae
open import Sets.FinSet
open import Functions
open import Sets.EquivalenceRelations
open import Numbers.Naturals.Naturals
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Isomorphisms.Definition
open import Groups.Subgroups.Definition
open import Groups.Lemmas
open import Groups.Abelian.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Subgroups.Normal.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

normalSubgroup : {c : _} {pred : A → Set c} (sub : subgroup G pred) → Set (a ⊔ c)
normalSubgroup {pred = pred} sub = {g k : A} → pred k → pred (g + (k + Group.inverse G g))
