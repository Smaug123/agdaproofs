{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Vectors
open import Semirings.Definition
open import Categories.Definition

module Categories.Functor.Definition where

record Functor {a b c d : _} (C : Category {a} {b}) (D : Category {c} {d}) : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    onObj : Category.objects C → Category.objects D
    onArrow : {S T : Category.objects C} → Category.arrows C S T → Category.arrows D (onObj S) (onObj T)
    mapId : {T : Category.objects C} → onArrow (Category.id C T) ≡ Category.id D (onObj T)
    mapCompose : {X Y Z : Category.objects C} → (f : Category.arrows C X Y) (g : Category.arrows C Y Z) → onArrow (Category._∘_ C g f) ≡ Category._∘_ D (onArrow g) (onArrow f)
