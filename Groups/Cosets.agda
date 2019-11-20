{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Setoids.Subset
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Groups.Definition
open import Groups.Subgroups.Definition
open import Groups.Subgroups.Normal.Definition

module Groups.Cosets {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) {c : _} {pred : A → Set c} (subgrp : subgroup G pred) where

open Equivalence (Setoid.eq S)
open import Groups.Lemmas G
open _&_&_ (_&&_.snd subgrp)
open Group G

private
  subs = _&&_.fst subgrp

cosetSetoid : Setoid A
Setoid._∼_ cosetSetoid g h = pred ((Group.inverse G h) + g)
Equivalence.reflexive (Setoid.eq cosetSetoid) = subs (symmetric (Group.invLeft G)) two
Equivalence.symmetric (Setoid.eq cosetSetoid) yx = subs (transitive invContravariant (+WellDefined reflexive invInv)) (three yx)
Equivalence.transitive (Setoid.eq cosetSetoid) yx zy = subs (transitive +Associative (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) reflexive)) (one zy yx)

cosetGroup : normalSubgroup G subgrp → Group cosetSetoid _+_
Group.+WellDefined (cosetGroup norm) {m} {n} {x} {y} m=x n=y = ans
  where
    t : pred (inverse y + n)
    t = n=y
    u : pred (inverse x + m)
    u = m=x
    v : pred (m + inverse x)
    v = subs (+WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight))) (norm u)
    ans' : pred ((inverse y) + ((inverse x + m) + inverse (inverse y)))
    ans' = norm u
    ans'' : pred ((inverse y) + ((inverse x + m) + y))
    ans'' = subs (+WellDefined reflexive (+WellDefined reflexive (invTwice y))) ans'
    ans : pred (inverse (x + y) + (m + n))
    ans = subs (transitive (transitive +Associative (transitive (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight))) +Associative)) reflexive) (symmetric +Associative))) (symmetric (+WellDefined invContravariant reflexive))) (one ans'' t)
Group.0G (cosetGroup norm) = 0G
Group.inverse (cosetGroup norm) = inverse
Group.+Associative (cosetGroup norm) {a} {b} {c} = subs (symmetric (transitive (+WellDefined (inverseWellDefined (symmetric +Associative)) reflexive) (invLeft {a + (b + c)}))) two
Group.identRight (cosetGroup norm) = subs (symmetric (transitive +Associative (transitive (+WellDefined invLeft reflexive) identRight))) two
Group.identLeft (cosetGroup norm) = subs (symmetric (transitive (+WellDefined reflexive identLeft) invLeft)) two
Group.invLeft (cosetGroup norm) = subs (symmetric (transitive (+WellDefined reflexive invLeft) invLeft)) two
Group.invRight (cosetGroup norm) = subs (symmetric (transitive (+WellDefined reflexive invRight) invLeft)) two
