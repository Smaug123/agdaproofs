{-# OPTIONS --warning=error --safe --without-K #-}

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

open import Fields.Fields
open import Fields.FieldOfFractions
open import Fields.FieldOfFractionsOrder

open import Rings.Definition
open import Rings.Lemmas
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

module Everything.Safe where
