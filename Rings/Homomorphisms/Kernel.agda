{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Homomorphisms.Kernel {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_+1_ _*1_ : A → A → A} {_+2_ _*2_ : B → B → B} {R1 : Ring S _+1_ _*1_} {R2 : Ring T _+2_ _*2_} {f : A → B} (fHom : RingHom R1 R2 f) where

ringKernel : Set (a ⊔ d)
ringKernel = Sg A (λ a → Setoid._∼_ T (f a) (Ring.0R R2))
