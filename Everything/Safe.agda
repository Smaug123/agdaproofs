{-# OPTIONS --warning=error --safe --without-K --guardedness #-}

-- This file contains everything that can be compiled in --safe mode.

open import Numbers.Naturals.Naturals
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Multiplication
open import Numbers.BinaryNaturals.Order
open import Numbers.BinaryNaturals.Subtraction

open import Numbers.Modulo.Group

open import Numbers.Integers.Integers
open import Numbers.Integers.RingStructure.EuclideanDomain

open import Lists.Lists
open import Lists.Filter.AllTrue

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
open import Groups.Subgroups.Normal.Examples

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
open import Rings.IntegralDomains.Definition
open import Rings.DirectSum
open import Rings.Polynomial.Ring
open import Rings.Polynomial.Evaluation
open import Rings.Ideals.Definition
open import Rings.Isomorphisms.Definition
open import Rings.Quotients.Definition
open import Rings.Cosets
open import Rings.EuclideanDomains.Definition
open import Rings.EuclideanDomains.Examples
open import Rings.Homomorphisms.Image
open import Rings.Homomorphisms.Kernel
open import Rings.Ideals.FirstIsomorphismTheorem
open import Rings.Ideals.Lemmas
open import Rings.Ideals.Prime.Definition
open import Rings.Ideals.Prime.Lemmas
open import Rings.Ideals.Principal.Definition
open import Rings.IntegralDomains.Examples
open import Rings.PrincipalIdealDomains.Lemmas
open import Rings.Subrings.Definition
open import Rings.Ideals.Maximal.Lemmas
open import Rings.Primes.Lemmas
open import Rings.Irreducibles.Definition
open import Rings.Divisible.Definition
open import Rings.Associates.Lemmas

open import Setoids.Setoids
open import Setoids.DirectSum
open import Setoids.Lists
open import Setoids.Orders
open import Setoids.Functions.Definition
open import Setoids.Functions.Extension

open import Sets.Cardinality.Infinite.Examples
open import Sets.Cardinality.Infinite.Lemmas
open import Sets.Cardinality.Countable.Lemmas
open import Sets.Cardinality.Finite.Lemmas
open import Sets.FinSet.Lemmas

open import Decidable.Sets
open import Decidable.Relations

open import Vectors
open import Vectors.VectorSpace

open import KeyValue.KeyValue
open import KeyValue.LinearStore.Definition

open import Maybe
open import Orders.Total.Lemmas
open import Orders.WellFounded.Induction

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
