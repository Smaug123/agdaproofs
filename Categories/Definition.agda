{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Categories.Definition where

record Category {a b : _} : Set (lsuc (a ⊔ b)) where
  field
    objects : Set a
    arrows : objects → objects → Set b
    id : (x : objects) → arrows x x
    _∘_ : {x y z : objects} → arrows y z → arrows x y → arrows x z
    rightId : {x y : objects} → (f : arrows x y) → (id y) ∘ f ≡ f
    leftId : {x y : objects} → (f : arrows x y) → f ∘ (id x) ≡ f
    compositionAssociative : {x y z w : objects} → (f : arrows z w) → (g : arrows y z) → (h : arrows x y) → (f ∘ (g ∘ h)) ≡ (f ∘ g) ∘ h
