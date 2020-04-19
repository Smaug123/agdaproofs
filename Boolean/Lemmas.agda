{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Boolean.Definition

module Boolean.Lemmas where

notNot : (x : Bool) → not (not x) ≡ x
notNot BoolTrue = refl
notNot BoolFalse = refl

notXor : (x y : Bool) → not (xor x y) ≡ xor (not x) y
notXor BoolTrue BoolTrue = refl
notXor BoolTrue BoolFalse = refl
notXor BoolFalse BoolTrue = refl
notXor BoolFalse BoolFalse = refl
