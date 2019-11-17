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

module Rings.Polynomial.Group {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Polynomial.Definition R
open import Rings.Polynomial.Addition R

polyGroup : Group naivePolySetoid _+P_
Group.+WellDefined polyGroup = +PwellDefined
Group.0G polyGroup = []
Group.inverse polyGroup = {!!}
Group.+Associative polyGroup = {!!}
Group.identRight polyGroup = {!!}
Group.identLeft polyGroup = {!!}
Group.invLeft polyGroup = {!!}
Group.invRight polyGroup = {!!}
