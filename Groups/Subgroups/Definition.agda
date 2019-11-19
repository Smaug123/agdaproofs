{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Groups.Homomorphisms.Definition

module Groups.Subgroups.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open Group G

subgroup : {c : _} {pred : A → Set c} → (wd : {x y : A} → (Setoid._∼_ S x y) → (pred x → pred y)) → Set (a ⊔ c)
subgroup {pred = pred} wd = ({g h : A} → (pred g) → (pred h) → pred (g + h)) & pred 0G & ({g : A} → (pred g) → (pred (inverse g)))
