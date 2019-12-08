{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Semiring -- for length
open import Numbers.Naturals.Order
open import Semirings.Definition
open import Lists.Definition
open import Lists.Fold.Fold

module Lists.Length where

length : {a : _} {A : Set a} (l : List A) → ℕ
length [] = zero
length (x :: l) = succ (length l)

length' : {a : _} {A : Set a} → (l : List A) → ℕ
length' = fold (λ _ → succ) 0

length=length' : {a : _} {A : Set a} (l : List A) → length l ≡ length' l
length=length' [] = refl
length=length' (x :: l) = applyEquality succ (length=length' l)
