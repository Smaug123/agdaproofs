{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Groups.Abelian.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Modules.Definition
open import Fields.Fields

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Vectors.VectorSpace {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+R_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+R_ _*_) {m n : _} {M : Set m} {T : Setoid {m} {n} M} {_+_ : M → M → M} {G' : Group T _+_} (G : AbelianGroup G') (_·_ : A → M → M) where

record VectorSpace : Set (lsuc a ⊔ b ⊔ m ⊔ n) where
  field
    isModule : Module R G _·_
    isField : Field R
