{-# OPTIONS --warning=error --safe --without-K #-}

open import Functions.Definition
open import Groups.Definition
open import Rings.Homomorphisms.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Sets.EquivalenceRelations
open import Groups.Lemmas
open import Rings.Ideals.Definition

module Rings.Cosets {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) {pred : A → Set c} (ideal : Ideal R pred) where

open Ring R
open import Rings.Lemmas R
open import Groups.Subgroups.Normal.Lemmas

open import Groups.Cosets additiveGroup (Ideal.isSubgroup ideal)

open Setoid S
open Equivalence eq
open Ideal ideal
open Group additiveGroup

cosetRing : Ring cosetSetoid _+_ _*_
Ring.additiveGroup cosetRing = cosetGroup (abelianGroupSubgroupIsNormal (Ideal.isSubgroup ideal) abelianUnderlyingGroup)
Ring.*WellDefined cosetRing {r} {s} {t} {u} r=t s=u = need
  where
    r=t' : pred ((inverse t + r) * u)
    r=t' = accumulatesTimes r=t
    s=u' : pred ((inverse u + s) * r)
    s=u' = accumulatesTimes s=u
    need : pred (inverse (t * u) + (r * s))
    need = isSubset (transitive (+WellDefined (*DistributesOver+') *DistributesOver+') (transitive +Associative (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined ringMinusExtracts' (transitive (+WellDefined reflexive (transitive ringMinusExtracts' (inverseWellDefined additiveGroup *Commutative))) invRight)) identRight)) *Commutative))) (closedUnderPlus r=t' s=u')
Ring.1R cosetRing = 1R
Ring.groupIsAbelian cosetRing = isSubset (transitive (symmetric invLeft) (+WellDefined (inverseWellDefined additiveGroup groupIsAbelian) reflexive)) containsIdentity
Ring.*Associative cosetRing = isSubset (transitive (symmetric invLeft) (+WellDefined (inverseWellDefined additiveGroup *Associative) reflexive)) containsIdentity
Ring.*Commutative cosetRing {a} {b} = isSubset (transitive (symmetric invLeft) (+WellDefined (inverseWellDefined additiveGroup *Commutative) reflexive)) containsIdentity
Ring.*DistributesOver+ cosetRing = isSubset (symmetric (transitive (+WellDefined (inverseWellDefined additiveGroup (symmetric *DistributesOver+)) reflexive) invLeft)) containsIdentity
Ring.identIsIdent cosetRing = isSubset (symmetric (transitive (Group.+WellDefined additiveGroup reflexive identIsIdent) invLeft)) containsIdentity

cosetRingHom : RingHom R cosetRing id
RingHom.preserves1 cosetRingHom = isSubset (symmetric invLeft) (Ideal.containsIdentity ideal)
RingHom.ringHom cosetRingHom = isSubset (symmetric invLeft) (Ideal.containsIdentity ideal)
RingHom.groupHom cosetRingHom = cosetGroupHom (abelianGroupSubgroupIsNormal (Ideal.isSubgroup ideal) abelianUnderlyingGroup)
