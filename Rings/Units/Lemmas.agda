{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition


module Rings.Units.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Units.Definition R
open import Rings.Ideals.Definition R

open Ring R
open Setoid S
open Equivalence eq

unitImpliesGeneratedIdealEverything : {x : A} → Unit x → {y : A} → generatedIdealPred x y
unitImpliesGeneratedIdealEverything {x} (a , xa=1) {y} = (a * y) , transitive *Associative (transitive (*WellDefined xa=1 reflexive) identIsIdent)
