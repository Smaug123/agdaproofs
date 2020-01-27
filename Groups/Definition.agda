{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Definition where

record Group {lvl1 lvl2} {A : Set lvl1} (S : Setoid {lvl1} {lvl2} A) (_·_ : A → A → A) : Set (lsuc lvl1 ⊔ lvl2) where
  open Setoid S
  field
    +WellDefined : {m n x y : A} → (m ∼ x) → (n ∼ y) → (m · n) ∼ (x · y)
    0G : A
    inverse : A → A
    +Associative : {a b c : A} → (a · (b · c)) ∼ (a · b) · c
    identRight : {a : A} → (a · 0G) ∼ a
    identLeft : {a : A} → (0G · a) ∼ a
    invLeft : {a : A} → (inverse a) · a ∼ 0G
    invRight : {a : A} → a · (inverse a) ∼ 0G
