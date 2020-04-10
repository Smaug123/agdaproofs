{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition

module Rings.Divisible.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Setoid S
open Equivalence eq
open Ring R
open import Rings.Divisible.Definition R
open import Rings.Units.Definition R

divisionTransitive : (x y z : A) → x ∣ y → y ∣ z → x ∣ z
divisionTransitive x y z (a , pr) (b , pr2) = (a * b) , transitive (transitive *Associative (*WellDefined pr reflexive)) pr2

divisionReflexive : (x : A) → x ∣ x
divisionReflexive x = 1R , transitive *Commutative identIsIdent

everythingDividesZero : (r : A) → r ∣ 0R
everythingDividesZero r = 0R , timesZero

nonzeroInherits : {x y : A} (nz : (x ∼ 0R) → False) → y ∣ x → (y ∼ 0R) → False
nonzeroInherits {x} {y} nz (c , pr) y=0 = nz (transitive (symmetric pr) (transitive (*WellDefined y=0 reflexive) (transitive *Commutative timesZero)))

nonunitInherits : {x y : A} (nonunit : Unit x → False) → x ∣ y → Unit y → False
nonunitInherits nu (s , pr) (a , b) = nu ((s * a) , transitive (transitive *Associative (*WellDefined pr reflexive)) b)
