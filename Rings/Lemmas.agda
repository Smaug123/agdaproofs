{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Abelian.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations

module Rings.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) where

abstract

  open Setoid S
  open Ring R
  open Group additiveGroup

  ringMinusExtracts : {x y : A} → Setoid._∼_ S (x * Group.inverse (Ring.additiveGroup R) y) (Group.inverse (Ring.additiveGroup R) (x * y))
  ringMinusExtracts {x = x} {y} = transferToRight' additiveGroup (transitive (symmetric *DistributesOver+) (transitive (*WellDefined reflexive invLeft) (Ring.timesZero R)))
    where
      open Equivalence eq

  ringMinusExtracts' : {x y : A} → ((inverse x) * y) ∼ inverse (x * y)
  ringMinusExtracts' {x = x} {y} = transitive *Commutative (transitive ringMinusExtracts (inverseWellDefined additiveGroup *Commutative))
    where
      open Equivalence eq

  twoNegativesTimes : {a b : A} → (inverse a) * (inverse b) ∼ a * b
  twoNegativesTimes {a} {b} = transitive (ringMinusExtracts) (transitive (inverseWellDefined additiveGroup ringMinusExtracts') (invTwice additiveGroup (a * b)))
    where
      open Equivalence eq

  groupLemmaMove0G : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → (Setoid._∼_ S (Group.0G G) (Group.inverse G x)) → Setoid._∼_ S x (Group.0G G)
  groupLemmaMove0G {S = S} G {x} pr = transitive (symmetric (invInv G)) (transitive (symmetric p) (invIdent G))
    where
      open Equivalence (Setoid.eq S)
      p : Setoid._∼_ S (Group.inverse G (Group.0G G)) (Group.inverse G (Group.inverse G x))
      p = inverseWellDefined G pr

  groupLemmaMove0G' : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → Setoid._∼_ S x (Group.0G G) → (Setoid._∼_ S (Group.0G G) (Group.inverse G x))
  groupLemmaMove0G' {S = S} G {x} pr = transferToRight' G (Equivalence.transitive (Setoid.eq S) (Group.identLeft G) pr)

  oneZeroImpliesAllZero : 0R ∼ 1R → {x : A} → x ∼ 0R
  oneZeroImpliesAllZero 0=1 = Equivalence.transitive eq (Equivalence.symmetric eq identIsIdent) (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=1) (Equivalence.reflexive eq)) (Equivalence.transitive eq *Commutative timesZero))

  lemm3 : (a b : A) → 0G ∼ (a + b) → 0G ∼ a → 0G ∼ b
  lemm3 a b pr1 pr2 with transferToRight' additiveGroup (Equivalence.symmetric eq pr1)
  ... | a=-b with Equivalence.transitive eq pr2 a=-b
  ... | 0=-b with inverseWellDefined additiveGroup 0=-b
  ... | -0=--b = Equivalence.transitive eq (Equivalence.symmetric eq (invIdent additiveGroup)) (Equivalence.transitive eq -0=--b (invTwice additiveGroup b))

  charNot2ImpliesNontrivial : ((1R + 1R) ∼ 0R → False) → (0R ∼ 1R) → False
  charNot2ImpliesNontrivial charNot2 0=1 = charNot2 (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq 0=1) (Equivalence.symmetric eq 0=1)) identRight)

abelianUnderlyingGroup : AbelianGroup additiveGroup
abelianUnderlyingGroup = record { commutative = groupIsAbelian }
