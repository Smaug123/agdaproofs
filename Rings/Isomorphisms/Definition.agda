{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Rings.Definition
open import Rings.Homomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Isomorphisms.Definition {a b c d : _} {A : Set a} {S : Setoid {a} {b} A} {_+1_ _*1_ : A → A → A} (R1 : Ring S _+1_ _*1_) {B : Set c} {T : Setoid {c} {d} B} {_+2_ _*2_ : B → B → B} (R2 : Ring T _+2_ _*2_) where

record RingIso (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    ringHom : RingHom R1 R2 f
    bijective : SetoidBijection S T f

record RingsIsomorphic : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    f : A → B
    iso : RingIso f
