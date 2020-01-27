{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Setoids
open import Groups.Subgroups.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Subgroups.Normal.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

normalSubgroup : {c : _} {pred : A → Set c} (sub : Subgroup G pred) → Set (a ⊔ c)
normalSubgroup {pred = pred} sub = {g k : A} → pred k → pred (g + (k + Group.inverse G g))
