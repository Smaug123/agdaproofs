{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Setoids.Setoids
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Homomorphisms.Definition where

record RingHom {m n o p : _} {A : Set m} {B : Set n} {SA : Setoid {m} {o} A} {SB : Setoid {n} {p} B} {_+A_ : A → A → A} {_*A_ : A → A → A} (R : Ring SA _+A_ _*A_) {_+B_ : B → B → B} {_*B_ : B → B → B} (S : Ring SB _+B_ _*B_) (f : A → B) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Ring S
  open Group additiveGroup
  open Setoid SB
  field
    preserves1 : f (Ring.1R R) ∼ 1R
    ringHom : {r s : A} → f (r *A s) ∼ (f r) *B (f s)
    groupHom : GroupHom (Ring.additiveGroup R) additiveGroup f
