{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Groups.Definition

module Rings.Orders.Total.Bounded {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (tRing : TotallyOrderedRing pRing) where

open import Rings.Orders.Partial.Bounded pRing
open Ring R
open Group additiveGroup
open import Groups.Lemmas (Ring.additiveGroup R)
open Setoid S
open Equivalence eq
open SetoidPartialOrder pOrder
open import Rings.Orders.Total.Lemmas tRing
open PartiallyOrderedRing pRing

boundGreaterThanZero : {s : Sequence A} → (b : Bounded s) → 0G < underlying b
boundGreaterThanZero {s} (a , b) with b 0
... | (l ,, r) = halvePositive a (<WellDefined invLeft reflexive (orderRespectsAddition (<Transitive l r) a))
