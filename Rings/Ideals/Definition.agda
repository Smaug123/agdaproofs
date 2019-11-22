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

module Rings.Ideals.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Groups.Subgroups.Definition (Ring.additiveGroup R)

record Ideal {c : _} (pred : A → Set c) : Set (a ⊔ b ⊔ c) where
  field
    isSubgroup : Subgroup pred
    accumulatesTimes : {x : A} → {y : A} → pred x → pred (x * y)
  closedUnderPlus = Subgroup.closedUnderPlus isSubgroup
  closedUnderInverse = Subgroup.closedUnderInverse isSubgroup
  containsIdentity = Subgroup.containsIdentity isSubgroup
  isSubset = Subgroup.isSubset isSubgroup
