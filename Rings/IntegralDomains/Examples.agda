{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Lemmas
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Orders
open import Setoids.Setoids
open import Functions
open import Rings.Definition
open import Rings.Lemmas
open import Sets.EquivalenceRelations
open import Rings.IntegralDomains.Definition
open import Fields.Fields

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.IntegralDomains.Examples where

fieldIsIntDom : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) → (Setoid._∼_ S (Ring.1R R) (Ring.0R R) → False) → IntegralDomain R
IntegralDomain.intDom (fieldIsIntDom F 1!=0) {a} {b} ab=0 a!=0 with Field.allInvertible F a a!=0
IntegralDomain.intDom (fieldIsIntDom {S = S} {R = R} F _) {a} {b} ab=0 a!=0 | 1/a , prA = transitive (symmetric identIsIdent) (transitive (*WellDefined (symmetric prA) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive ab=0) timesZero)))
  where
    open Setoid S
    open Equivalence eq
    open Ring R
IntegralDomain.nontrivial (fieldIsIntDom F 1!=0) = 1!=0
