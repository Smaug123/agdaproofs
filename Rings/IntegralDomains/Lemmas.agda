{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Sets.EquivalenceRelations
open import Rings.IntegralDomains.Definition

module Rings.IntegralDomains.Lemmas {m n : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open Setoid S
open Equivalence eq
open Ring R

cancelIntDom : {a b c : A} → (a * b) ∼ (a * c) → ((a ∼ (Ring.0R R)) → False) → (b ∼ c)
cancelIntDom {a} {b} {c} ab=ac a!=0 = transferToRight (Ring.additiveGroup R) t3
  where
    t1 : (a * b) + Group.inverse (Ring.additiveGroup R) (a * c) ∼ Ring.0R R
    t1 = transferToRight'' (Ring.additiveGroup R) ab=ac
    t2 : a * (b + Group.inverse (Ring.additiveGroup R) c) ∼ Ring.0R R
    t2 = transitive (transitive (Ring.*DistributesOver+ R) (Group.+WellDefined (Ring.additiveGroup R) reflexive (transferToRight' (Ring.additiveGroup R) (transitive (symmetric (Ring.*DistributesOver+ R)) (transitive (Ring.*WellDefined R reflexive (Group.invLeft (Ring.additiveGroup R))) (Ring.timesZero R)))))) t1
    t3 : (b + Group.inverse (Ring.additiveGroup R) c) ∼ Ring.0R R
    t3 = IntegralDomain.intDom I t2 a!=0

cancelIntDom' : {a b c : A} → (a * c) ∼ (b * c) → (c ∼ Ring.0R R → False) → a ∼ b
cancelIntDom' pr n = cancelIntDom (transitive *Commutative (transitive pr *Commutative)) n
