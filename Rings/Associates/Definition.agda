{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions.Definition
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.IntegralDomains.Definition

module Rings.Associates.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Units.Definition R
open Setoid S
open Ring R
open Equivalence eq

Associates : Rel A
Associates x y = Sg A (λ z → Unit z && (x ∼ (y * z)))
