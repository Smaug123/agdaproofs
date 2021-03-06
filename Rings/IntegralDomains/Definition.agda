{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
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
