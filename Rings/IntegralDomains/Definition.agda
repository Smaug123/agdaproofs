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

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.IntegralDomains.Definition {m n : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Setoid S
open Equivalence eq
open Ring R

record IntegralDomain : Set (lsuc m ⊔ n) where
  field
    intDom : {a b : A} → (a * b) ∼ (Ring.0R R) → ((a ∼ (Ring.0R R)) → False) → b ∼ (Ring.0R R)
    nontrivial : Setoid._∼_ S (Ring.1R R) (Ring.0R R) → False

decidedIntDom : ({a b : A} → (a * b) ∼ (Ring.0R R) → (a ∼ 0R) || (b ∼ 0R)) → ({a b : A} → (a * b) ∼ 0R → ((a ∼ (Ring.0R R)) → False) → b ∼ (Ring.0R R))
decidedIntDom f ab=0 a!=0 with f ab=0
decidedIntDom f ab=0 a!=0 | inl x = exFalso (a!=0 x)
decidedIntDom f ab=0 a!=0 | inr x = x

cancelIntDom : (I : IntegralDomain) {a b c : A} → (a * b) ∼ (a * c) → ((a ∼ (Ring.0R R)) → False) → (b ∼ c)
cancelIntDom I {a} {b} {c} ab=ac a!=0 = transferToRight (Ring.additiveGroup R) t3
  where
    t1 : (a * b) + Group.inverse (Ring.additiveGroup R) (a * c) ∼ Ring.0R R
    t1 = transferToRight'' (Ring.additiveGroup R) ab=ac
    t2 : a * (b + Group.inverse (Ring.additiveGroup R) c) ∼ Ring.0R R
    t2 = transitive (transitive (Ring.*DistributesOver+ R) (Group.+WellDefined (Ring.additiveGroup R) reflexive (transferToRight' (Ring.additiveGroup R) (transitive (symmetric (Ring.*DistributesOver+ R)) (transitive (Ring.*WellDefined R reflexive (Group.invLeft (Ring.additiveGroup R))) (Ring.timesZero R)))))) t1
    t3 : (b + Group.inverse (Ring.additiveGroup R) c) ∼ Ring.0R R
    t3 = IntegralDomain.intDom I t2 a!=0
