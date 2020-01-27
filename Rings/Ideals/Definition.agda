{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Groups.Subgroups.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open Setoid S
open Equivalence eq
open Group additiveGroup

open import Rings.Lemmas R
open import Rings.Divisible.Definition R

record Ideal {c : _} (pred : A → Set c) : Set (a ⊔ b ⊔ c) where
  field
    isSubgroup : Subgroup additiveGroup pred
    accumulatesTimes : {x : A} → {y : A} → pred x → pred (x * y)
  closedUnderPlus = Subgroup.closedUnderPlus isSubgroup
  closedUnderInverse = Subgroup.closedUnderInverse isSubgroup
  containsIdentity = Subgroup.containsIdentity isSubgroup
  isSubset = Subgroup.isSubset isSubgroup
  predicate = pred

generatedIdealPred : A → A → Set (a ⊔ b)
generatedIdealPred a b = a ∣ b

generatedIdeal : (a : A) → Ideal (generatedIdealPred a)
Subgroup.isSubset (Ideal.isSubgroup (generatedIdeal a)) {x} {y} x=y (c , prC) = c , transitive prC x=y
Subgroup.closedUnderPlus (Ideal.isSubgroup (generatedIdeal a)) {g} {h} (c , prC) (d , prD) = (c + d) , transitive *DistributesOver+ (+WellDefined prC prD)
Subgroup.containsIdentity (Ideal.isSubgroup (generatedIdeal a)) = 0G , timesZero
Subgroup.closedUnderInverse (Ideal.isSubgroup (generatedIdeal a)) {g} (c , prC) = inverse c , transitive ringMinusExtracts (inverseWellDefined additiveGroup prC)
Ideal.accumulatesTimes (generatedIdeal a) {x} {y} (c , prC) = (c * y) , transitive *Associative (*WellDefined prC reflexive)
