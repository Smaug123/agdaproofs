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

module Rings.Lemmas where

ringMinusExtracts : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) → {x y : A} → Setoid._∼_ S (x * Group.inverse (Ring.additiveGroup R) y) (Group.inverse (Ring.additiveGroup R) (x * y))
ringMinusExtracts {S = S} {_+_ = _+_} {_*_ = _*_} R {x = x} {y} = transferToRight' additiveGroup (transitive (symmetric *DistributesOver+) (transitive (*WellDefined reflexive invLeft) (Ring.timesZero R)))
  where
    open Setoid S
    open Equivalence eq
    open Ring R
    open Group additiveGroup

groupLemmaMove0G : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → (Setoid._∼_ S (Group.0G G) (Group.inverse G x)) → Setoid._∼_ S x (Group.0G G)
groupLemmaMove0G {S = S} G {x} pr = transitive (symmetric (invInv G)) (transitive (symmetric p) (invIdent G))
  where
    open Group G
    open Setoid S
    open Equivalence eq
    p : inverse 0G ∼ inverse (inverse x)
    p = inverseWellDefined G pr

groupLemmaMove0G' : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → Setoid._∼_ S x (Group.0G G) → (Setoid._∼_ S (Group.0G G) (Group.inverse G x))
groupLemmaMove0G' {S = S} G {x} pr = transferToRight' G (transitive identLeft pr)
  where
    open Group G
    open Setoid S
    open Equivalence eq
