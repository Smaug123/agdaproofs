{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Sets.FinSet

module Groups.GroupDefinition where

  record Group {lvl1 lvl2} {A : Set lvl1} (S : Setoid {lvl1} {lvl2} A) (_·_ : A → A → A) : Set (lsuc lvl1 ⊔ lvl2) where
    open Setoid S
    field
      wellDefined : {m n x y : A} → (m ∼ x) → (n ∼ y) → (m · n) ∼ (x · y)
      identity : A
      inverse : A → A
      multAssoc : {a b c : A} → (a · (b · c)) ∼ (a · b) · c
      multIdentRight : {a : A} → (a · identity) ∼ a
      multIdentLeft : {a : A} → (identity · a) ∼ a
      invLeft : {a : A} → (inverse a) · a ∼ identity
      invRight : {a : A} → a · (inverse a) ∼ identity
