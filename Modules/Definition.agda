{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Groups.Abelian.Definition
open import Setoids.Setoids
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Modules.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+R_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+R_ _*_) {m n : _} {M : Set m} {T : Setoid {m} {n} M} {_+_ : M → M → M} {G' : Group T _+_} (G : AbelianGroup G') (_·_ : A → M → M) where

record Module : Set (a ⊔ b ⊔ m ⊔ n) where
  field
    dotWellDefined : {r s : A} {t u : M} → Setoid._∼_ S r s → Setoid._∼_ T t u → Setoid._∼_ T (r · t) (s · u)
    dotDistributesLeft : {r : A} {x y : M} → Setoid._∼_ T (r · (x + y)) ((r · x) + (r · y))
    dotDistributesRight : {r s : A} {x : M} → Setoid._∼_ T ((r +R s) · x) ((r · x) + (s · x))
    dotAssociative : {r s : A} {x : M} → Setoid._∼_ T ((r * s) · x) (r · (s · x))
    dotIdentity : {x : M} → Setoid._∼_ T ((Ring.1R R) · x) x
