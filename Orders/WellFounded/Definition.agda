{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions

module Orders.WellFounded.Definition {a b : _} {A : Set a} (_<_ : Rel {a} {b} A) where

data Accessible (x : A) : Set (lsuc a ⊔ b) where
  access : (∀ y → y < x → Accessible y) → Accessible x

WellFounded : Set (lsuc a ⊔ b)
WellFounded = ∀ x → Accessible x

