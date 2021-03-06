{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Groups.Definition

module Groups.Abelian.Definition where

record AbelianGroup {a} {b} {A : Set a} {S : Setoid {a} {b} A} {_·_ : A → A → A} (G : Group S _·_) : Set (lsuc a ⊔ b) where
  open Setoid S
  field
    commutative : {a b : A} → (a · b) ∼ (b · a)
