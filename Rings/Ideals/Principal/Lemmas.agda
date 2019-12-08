{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Principal.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Setoid S
open Ring R
open Equivalence eq
open import Rings.Ideals.Principal.Definition R
open import Rings.Ideals.Definition R
open import Rings.Ideals.Lemmas R
open import Rings.Divisible.Definition R

generatorZeroImpliesAllZero : {c : _} {pred : A → Set c} → {i : Ideal pred} → (princ : PrincipalIdeal i) → PrincipalIdeal.generator princ ∼ 0R → {x : A} → pred x → x ∼ 0R
generatorZeroImpliesAllZero record { generator = gen ; genIsInIdeal = genIsInIdeal ; genGenerates = genGenerates } gen=0 {x} predX = generatorZeroImpliesMembersZero {x} (divisibleWellDefined gen=0 reflexive (genGenerates predX))
