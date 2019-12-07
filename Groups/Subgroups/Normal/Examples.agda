{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Groups
open import Groups.Definition
open import Orders
open import Numbers.Integers.Integers
open import Setoids.Setoids
open import LogicalFormulae
open import Sets.FinSet
open import Functions
open import Sets.EquivalenceRelations
open import Numbers.Naturals.Naturals
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Isomorphisms.Definition
open import Groups.Subgroups.Definition
open import Groups.Lemmas
open import Groups.Abelian.Definition
open import Groups.QuotientGroup.Definition
open import Groups.Subgroups.Normal.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Subgroups.Normal.Examples {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Groups.Subgroups.Examples G
open Setoid S
open Equivalence eq
open Group G

trivialSubgroupIsNormal : normalSubgroup G trivialSubgroup
trivialSubgroupIsNormal {g} k=0 = transitive (+WellDefined reflexive (transitive (+WellDefined k=0 reflexive) identLeft)) (invRight {g})

improperSubgroupIsNormal : normalSubgroup G improperSubgroup
improperSubgroupIsNormal _ = record {}
