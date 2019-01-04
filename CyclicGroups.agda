{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Naturals
open import Integers
open import FinSet
open import Groups

module CyclicGroups where

    positiveEltPower : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) (x : A) (i : ℕ) → A
    positiveEltPower G x 0 = Group.identity G
    positiveEltPower {_·_ = _·_} G x (succ i) = x · (positiveEltPower G x i)

    positiveEltPowerCollapse : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} (G : Group S _+_) (x : A) (i j : ℕ) → Setoid._∼_ S ((positiveEltPower G x i) + (positiveEltPower G x j)) (positiveEltPower G x (i +N j))
    positiveEltPowerCollapse G x zero j = Group.multIdentLeft G
    positiveEltPowerCollapse {S = S} G x (succ i) j = transitive (symmetric multAssoc) (wellDefined reflexive (positiveEltPowerCollapse G x i j))
      where
        open Setoid S
        open Group G
        open Transitive (Equivalence.transitiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)
        open Reflexive (Equivalence.reflexiveEq eq)

    elementPower : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) (x : A) (i : ℤ) → A
    elementPower G x (nonneg i) = positiveEltPower G x i
    elementPower {_·_ = _·_} G x (negSucc i) = Group.inverse G (positiveEltPower G x (succ i))

    record CyclicGroup {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) : Set (m ⊔ n) where
      field
        generator : A
        cyclic : {a : A} → (Sg ℤ (λ i → Setoid._∼_ S (elementPower G generator i) a))

    elementPowerCollapse : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) (x : A) (i j : ℤ) → Setoid._∼_ S ((elementPower G x i) · (elementPower G x j)) (elementPower G x (i +Z j))
    elementPowerCollapse {S = S} {_+_} G x (nonneg a) (nonneg b) rewrite addingNonnegIsHom a b = positiveEltPowerCollapse G x a b
    elementPowerCollapse G x (nonneg a) (negSucc b) = {!!}
    elementPowerCollapse G x (negSucc a) (nonneg b) = {!!}
    elementPowerCollapse G x (negSucc a) (negSucc b) = {!!}

    elementPowerHom : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) (x : A) → GroupHom ℤGroup G (λ i → elementPower G x i)
    GroupHom.groupHom (elementPowerHom {S = S} G x) {a} {b} = symmetric (elementPowerCollapse G x a b)
      where
        open Setoid S
        open Group G
        open Symmetric (Equivalence.symmetricEq eq)
    GroupHom.wellDefined (elementPowerHom {S = S} G x) {.y} {y} refl = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))

    subgroupOfCyclicIsCyclic : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : B → A} {fHom : GroupHom H G f} → Subgroup G H fHom → CyclicGroup G → CyclicGroup H
    CyclicGroup.generator (subgroupOfCyclicIsCyclic {f = f} subgrp record { generator = generator ; cyclic = cyclic }) = {!f generator!}
    CyclicGroup.cyclic (subgroupOfCyclicIsCyclic subgrp gCyclic) = {!!}

-- Prefer to prove that subgroup of cyclic is cyclic, then deduce this like with abelian groups
{-
    cyclicIsGroupProperty : {m n o p : _} {A : Set m} {B : Set o} {S : Setoid {m} {n} A} {T : Setoid {o} {p} B} {_+_ : A → A → A} {_*_ : B → B → B} {G : Group S _+_} {H : Group T _*_} → GroupsIsomorphic G H → CyclicGroup G → CyclicGroup H
    CyclicGroup.generator (cyclicIsGroupProperty {H = H} iso G) = GroupsIsomorphic.isomorphism iso (CyclicGroup.generator G)
    CyclicGroup.cyclic (cyclicIsGroupProperty {H = H} iso G) {a} with GroupIso.surj (GroupsIsomorphic.proof iso) {a}
    CyclicGroup.cyclic (cyclicIsGroupProperty {H = H} iso G) {a} | a' , b with CyclicGroup.cyclic G {a'}
    ... | pow , prPow = pow , {!!}
    -}

-- Proof of abelianness of cyclic groups: a cyclic group is the image of elementPowerHom into Z, so is isomorphic to a subgroup of Z. All subgroups of an abelian group are abelian.
    cyclicGroupIsAbelian : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {G : Group S _+_} (cyclic : CyclicGroup G) → AbelianGroup G
    cyclicGroupIsAbelian cyclic = {!!}
