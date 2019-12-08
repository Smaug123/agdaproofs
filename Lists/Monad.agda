{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Lists.Definition
open import Lists.Fold.Fold
open import Lists.Concat
open import Lists.Length
open import Numbers.Naturals.Semiring

module Lists.Monad where

open import Lists.Map.Map public

flatten : {a : _} {A : Set a} → (l : List (List A)) → List A
flatten [] = []
flatten (l :: ls) = l ++ flatten ls

flatten' : {a : _} {A : Set a} → (l : List (List A)) → List A
flatten' = fold _++_ []

flatten=flatten' : {a : _} {A : Set a} (l : List (List A)) → flatten l ≡ flatten' l
flatten=flatten' [] = refl
flatten=flatten' (l :: ls) = applyEquality (l ++_) (flatten=flatten' ls)

lengthFlatten : {a : _} {A : Set a} (l : List (List A)) → length (flatten l) ≡ (fold _+N_ zero (map length l))
lengthFlatten [] = refl
lengthFlatten (l :: ls) rewrite lengthConcat l (flatten ls) | lengthFlatten ls = refl
