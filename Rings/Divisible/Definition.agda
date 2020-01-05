{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition


module Rings.Divisible.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Setoid S
open Equivalence eq
open Ring R

_∣_ : Rel A
a ∣ b = Sg A (λ c → (a * c) ∼ b)

divisibleWellDefined : {x y a b : A} → (x ∼ y) → (a ∼ b) → x ∣ a → y ∣ b
divisibleWellDefined x=y a=b (c , xc=a) = c , transitive (*WellDefined (symmetric x=y) reflexive) (transitive xc=a a=b)
