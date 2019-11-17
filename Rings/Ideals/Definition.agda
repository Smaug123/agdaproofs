{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

ringKernel : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → Set (a ⊔ d)
ringKernel {T = T} R2 {f} fHom = Sg A (λ a → Setoid._∼_ T (f a) (Ring.0R R2))
