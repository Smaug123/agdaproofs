{-# OPTIONS --warning=error --safe --without-K #-}

-- This file contains everything that can be compiled in --safe mode.

open import Numbers.Naturals
open import Numbers.BinaryNaturals.Definition

open import Lists.Lists

open import Groups.Groups
open import Groups.FinitePermutations
open import Groups.GroupsLemmas

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

open import Maybe
open import Orders
open import WellFoundedInduction

open import ClassicalLogic.ClassicalFive

module Everything.Safe where