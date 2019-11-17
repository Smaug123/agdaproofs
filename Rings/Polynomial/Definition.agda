{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Vectors
open import Lists.Lists
open import Maybe
open import Rings.Homomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Polynomial.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Setoid S
open Equivalence eq
open Ring R

open import Groups.Polynomials.Definition additiveGroup

1P : NaivePoly
1P = 1R :: []

inducedFunction : NaivePoly → A → A
inducedFunction [] a = 0R
inducedFunction (x :: p) a = x + (a * inducedFunction p a)
