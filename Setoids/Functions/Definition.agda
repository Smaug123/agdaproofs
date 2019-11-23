{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Setoids.Subset

module Setoids.Functions.Definition {a b c d : _} {A : Set a} {B : Set b} where

WellDefined : (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) → Set (a ⊔ c ⊔ d)
WellDefined S T f = {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)
