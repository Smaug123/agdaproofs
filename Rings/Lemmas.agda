{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Groups.Groups
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Setoids.Setoids
open import Setoids.Orders
open import Sets.EquivalenceRelations

module Rings.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) where

open Setoid S
open Ring R
open Group additiveGroup

ringMinusExtracts : {x y : A} → Setoid._∼_ S (x * Group.inverse (Ring.additiveGroup R) y) (Group.inverse (Ring.additiveGroup R) (x * y))
ringMinusExtracts {x = x} {y} = transferToRight' additiveGroup (transitive (symmetric *DistributesOver+) (transitive (*WellDefined reflexive invLeft) (Ring.timesZero R)))
  where
    open Equivalence eq

ringMinusExtracts' : {x y : A} → Setoid._∼_ S ((Group.inverse (Ring.additiveGroup R) x) * y) (Group.inverse (Ring.additiveGroup R) (x * y))
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
