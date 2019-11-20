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
open import Groups.Abelian.Lemmas
open import Groups.DirectSum.Definition
open import Groups.QuotientGroup.Definition
open import Groups.QuotientGroup.Lemmas
open import Groups.FiniteGroups.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Homomorphisms.Examples
open import Groups.Isomorphisms.Lemmas
open import Groups.FinitePermutations
open import Groups.Lemmas
open import Groups.FirstIsomorphismTheorem
open import Groups.SymmetricGroups.Definition
open import Groups.Actions.Stabiliser
open import Groups.Actions.Orbit
open import Groups.SymmetricGroups.Lemmas
open import Groups.ActionIsSymmetry
open import Groups.Cyclic.Definition
open import Groups.Cyclic.DefinitionLemmas
open import Groups.Polynomials.Examples
open import Groups.Cosets

open import Fields.Fields
open import Fields.Orders.Partial.Definition
open import Fields.Orders.Total.Definition
open import Fields.Orders.Lemmas
open import Fields.FieldOfFractions.Field
open import Fields.FieldOfFractions.Lemmas
open import Fields.FieldOfFractions.Order

open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Lemmas
open import Rings.Orders.Partial.Lemmas
open import Rings.IntegralDomains
open import Rings.DirectSum
open import Rings.Polynomial.Ring
open import Rings.Polynomial.Evaluation
open import Rings.Ideals.Definition
open import Rings.Isomorphisms.Definition
open import Rings.Quotients.Definition

open import Setoids.Setoids
open import Setoids.DirectSum
open import Setoids.Lists
open import Setoids.Orders
open import Setoids.Functions.Definition
open import Setoids.Functions.Extension

open import Sets.Cardinality
open import Sets.FinSet

open import DecidableSet

open import Vectors
open import Vectors.VectorSpace

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

open import Categories.Definition
open import Categories.Functor.Definition
open import Categories.Functor.Lemmas
open import Categories.Dual.Definition

open import Modules.Examples
open import Modules.Lemmas
open import Modules.DirectSum

module Everything.Safe where
