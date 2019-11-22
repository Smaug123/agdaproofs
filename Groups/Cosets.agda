{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Setoids.Subset
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Groups.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Subgroups.Definition
open import Groups.Subgroups.Normal.Definition

module Groups.Cosets {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) {c : _} {pred : A → Set c} (subgrp : Subgroup G pred) where

open Equivalence (Setoid.eq S)
open import Groups.Lemmas G
open Group G
open Subgroup subgrp

cosetSetoid : Setoid A
Setoid._∼_ cosetSetoid g h = pred ((Group.inverse G h) + g)
Equivalence.reflexive (Setoid.eq cosetSetoid) = isSubset (symmetric (Group.invLeft G)) containsIdentity
Equivalence.symmetric (Setoid.eq cosetSetoid) yx = isSubset (transitive invContravariant (+WellDefined reflexive invInv)) (closedUnderInverse yx)
Equivalence.transitive (Setoid.eq cosetSetoid) yx zy = isSubset (transitive +Associative (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) reflexive)) (closedUnderPlus zy yx)

cosetGroup : normalSubgroup G subgrp → Group cosetSetoid _+_
Group.+WellDefined (cosetGroup norm) {m} {n} {x} {y} m=x n=y = ans
  where
    t : pred (inverse y + n)
    t = n=y
    u : pred (inverse x + m)
    u = m=x
    v : pred (m + inverse x)
    v = isSubset (+WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight))) (norm u)
    ans' : pred ((inverse y) + ((inverse x + m) + inverse (inverse y)))
    ans' = norm u
    ans'' : pred ((inverse y) + ((inverse x + m) + y))
    ans'' = isSubset (+WellDefined reflexive (+WellDefined reflexive (invTwice y))) ans'
    ans : pred (inverse (x + y) + (m + n))
    ans = isSubset (transitive (transitive +Associative (transitive (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight))) +Associative)) reflexive) (symmetric +Associative))) (symmetric (+WellDefined invContravariant reflexive))) (closedUnderPlus ans'' t)
Group.0G (cosetGroup norm) = 0G
Group.inverse (cosetGroup norm) = inverse
Group.+Associative (cosetGroup norm) {a} {b} {c} = isSubset (symmetric (transitive (+WellDefined (inverseWellDefined (symmetric +Associative)) reflexive) (invLeft {a + (b + c)}))) containsIdentity
Group.identRight (cosetGroup norm) = isSubset (symmetric (transitive +Associative (transitive (+WellDefined invLeft reflexive) identRight))) containsIdentity
Group.identLeft (cosetGroup norm) = isSubset (symmetric (transitive (+WellDefined reflexive identLeft) invLeft)) containsIdentity
Group.invLeft (cosetGroup norm) = isSubset (symmetric (transitive (+WellDefined reflexive invLeft) invLeft)) containsIdentity
Group.invRight (cosetGroup norm) = isSubset (symmetric (transitive (+WellDefined reflexive invRight) invLeft)) containsIdentity

cosetGroupHom : (norm : normalSubgroup G subgrp) → GroupHom G (cosetGroup norm) id
GroupHom.groupHom (cosetGroupHom norm) = isSubset (symmetric (transitive (+WellDefined invContravariant reflexive) (transitive +Associative (transitive (+WellDefined (transitive (symmetric +Associative) (+WellDefined reflexive invLeft)) reflexive) (transitive (+WellDefined identRight reflexive) invLeft))))) (Subgroup.containsIdentity subgrp)
GroupHom.wellDefined (cosetGroupHom norm) {x} {y} x=y = isSubset (symmetric (transitive (+WellDefined reflexive x=y) invLeft)) (Subgroup.containsIdentity subgrp)
