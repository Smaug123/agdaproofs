{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Vectors
open import Semirings.Definition
open import Categories.Definition
open import Groups.Definition

module Categories.Examples where

SET : {a : _} → Category {lsuc a} {a}
Category.objects (SET {a}) = Set a
Category.arrows (SET {a}) = λ a b → (a → b)
Category.id (SET {a}) = λ x → λ y → y
Category._∘_ (SET {a}) = λ f g → λ x → f (g x)
Category.rightId (SET {a}) = λ f → refl
Category.leftId (SET {a}) = λ f → refl
Category.compositionAssociative (SET {a}) = λ f g h → refl

GROUP : {a : _} → Category {lsuc a} {a}
Category.objects (GROUP {a}) = Group {!   !} {!   !}
Category.arrows (GROUP {a}) = {!   !}
Category.id (GROUP {a}) = {!   !}
Category._∘_ (GROUP {a}) = {!   !}
Category.rightId (GROUP {a}) = {!   !}
Category.leftId (GROUP {a}) = {!   !}
Category.compositionAssociative (GROUP {a}) = {!   !}
