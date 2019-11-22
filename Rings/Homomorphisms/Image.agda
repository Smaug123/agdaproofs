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

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Homomorphisms.Image {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_+A_ _*A_ : A → A → A} {_+B_ _*B_ : B → B → B} {R1 : Ring S _+A_ _*A_} {R2 : Ring T _+B_ _*B_} {f : A → B} (hom : RingHom R1 R2 f) where

open import Groups.Homomorphisms.Image (RingHom.groupHom hom)
open import Rings.Subrings.Definition

imageGroupSubring : Subring R2 imageGroupPred
Subring.isSubgroup imageGroupSubring = imageGroupSubgroup
Subring.containsOne imageGroupSubring = Ring.1R R1 , RingHom.preserves1 hom
Subring.closedUnderProduct imageGroupSubring {x} {y} (a , fa=x) (b , fb=y) = (a *A b) , transitive ringHom (Ring.*WellDefined R2 fa=x fb=y)
  where
    open Setoid T
    open Equivalence eq
    open RingHom hom
