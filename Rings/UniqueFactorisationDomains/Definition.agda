{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Lists.Lists

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.UniqueFactorisationDomains.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Units.Definition R
open import Rings.Irreducibles.Definition intDom
open Ring R
open Setoid S

record Factorisation {r : A} (nonzero : (r ∼ 0R) → False) (nonunit : (Unit r) → False) : Set (a ⊔ b) where
  field
    factorise : List A
    factoriseIsFactorisation : fold (_*_) 1R factorise ∼ r
    factoriseIsIrreducibles : allTrue Irreducible factorise

--record UFD : Set (a ⊔ b) where
--  field
--    factorisation : {r : A} → (nonzero : (r ∼ 0R) → False) → (nonunit : (Unit r) → False) → Factorisation nonzero nonunit
--    uniqueFactorisation : {r : A} → (nonzero : (r ∼ 0R) → False) → (nonunit : (Unit r) → False) → (f1 f2 : Factorisation nonzero nonunit) → {!Sg !}
