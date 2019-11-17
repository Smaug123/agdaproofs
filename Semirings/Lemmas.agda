{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Monoids.Definition
open import Semirings.Definition

module Semirings.Lemmas {a : _} {A : Set a} {Zero One : A} {_+_ _*_ : A → A → A} (S : Semiring Zero One _+_ _*_) where

open Semiring S

doubleIsAddTwo : (a : A) → (a + a) ≡ (One + One) * a
doubleIsAddTwo a = transitivity (equalityCommutative (+WellDefined (productOneLeft a) (productOneLeft a))) (equalityCommutative (+DistributesOver*' One One a))
