{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Groups.Subgroups.Normal.Definition


module Groups.Subgroups.Normal.Examples {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Groups.Subgroups.Examples G
open Setoid S
open Equivalence eq
open Group G

trivialSubgroupIsNormal : normalSubgroup G trivialSubgroup
trivialSubgroupIsNormal {g} k=0 = transitive (+WellDefined reflexive (transitive (+WellDefined k=0 reflexive) identLeft)) (invRight {g})

improperSubgroupIsNormal : normalSubgroup G improperSubgroup
improperSubgroupIsNormal _ = record {}
