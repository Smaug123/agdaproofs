{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids

module Setoids.Functions.Definition where

WellDefined : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) → Set (a ⊔ c ⊔ d)
WellDefined {A = A} S T f = {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)

