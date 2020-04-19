{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Decidable.Relations
open import Boolean.Definition

module Decidable.Reduction where

squash : {a b : _} {A : Set a} {f : A → Set b} → DecidableRelation f → A → Bool
squash rel a with rel a
... | inl x = BoolTrue
... | inr x = BoolFalse

unsquash : {a b : _} {A : Set a} {f : A → Set b} → (rel : DecidableRelation f) → {x : A} → .(squash rel x ≡ BoolTrue) → f x
unsquash rel {x} pr with rel x
... | inl ans = ans
