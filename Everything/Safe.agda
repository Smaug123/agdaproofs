{-# OPTIONS --warning=error --safe --without-K --guardedness #-}

-- This file contains everything that can be compiled in --safe mode.

open import Numbers.Naturals.Naturals
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Multiplication
open import Numbers.BinaryNaturals.Order
open import Numbers.BinaryNaturals.Subtraction

open import Numbers.Integers.Integers

open import Lists.Lists

open import Groups.Groups
open import Groups.FinitePermutations
open import Groups.Lemmas
open import Groups.Groups2
open import Groups.SymmetryGroups

open import Fields.Fields
open import Fields.Orders.Definition
open import Fields.Orders.Lemmas
open import Fields.FieldOfFractions
open import Fields.FieldOfFractionsOrder

open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Definition
open import Rings.Orders.Lemmas
open import Rings.IntegralDomains

open import Setoids.Setoids
open import Setoids.Lists
open import Setoids.Orders

open import Sets.Cardinality
open import Sets.FinSet

open import DecidableSet

open import Vectors

open import KeyValue.KeyValue
open import KeyValue.LinearStore.Definition

open import Maybe
open import Orders
open import WellFoundedInduction

open import ClassicalLogic.ClassicalFive

open import Monoids.Definition

open import Semirings.Definition
open import Semirings.Solver

open import Fields.CauchyCompletion.Group
open import Fields.CauchyCompletion.Ring

module Everything.Safe where

