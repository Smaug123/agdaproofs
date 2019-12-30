{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Groups.Definition

module Groups.Subgroups.Examples {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Groups.Subgroups.Definition G
open import Groups.Lemmas G

open Group G
open Setoid S
open Equivalence eq

trivialSubgroupPred : A → Set b
trivialSubgroupPred a = (a ∼ 0G)

trivialSubgroup : Subgroup trivialSubgroupPred
Subgroup.isSubset trivialSubgroup x=y x=0 = transitive (symmetric x=y) x=0
Subgroup.closedUnderPlus trivialSubgroup x=0 y=0 = transitive (+WellDefined x=0 y=0) identLeft
Subgroup.containsIdentity trivialSubgroup = reflexive
Subgroup.closedUnderInverse trivialSubgroup x=0 = transitive (inverseWellDefined x=0) invIdent

improperSubgroupPred : A → Set
improperSubgroupPred a = True

improperSubgroup : Subgroup improperSubgroupPred
Subgroup.isSubset improperSubgroup _ _ = record {}
Subgroup.closedUnderPlus improperSubgroup _ _ = record {}
Subgroup.containsIdentity improperSubgroup = record {}
Subgroup.closedUnderInverse improperSubgroup _ = record {}
