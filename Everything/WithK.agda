{-# OPTIONS --warning=error --safe --guardedness #-}

open import Everything.Safe

-- This file contains everything that is --safe, but uses K.
open import Numbers.Primes.PrimeNumbers
open import Numbers.Primes.IntegerFactorisation
open import Numbers.Rationals.Definition
open import Numbers.Rationals.Lemmas

open import Numbers.Reals.Definition

open import Logic.PropositionalLogic
open import Logic.PropositionalLogicExamples
open import Logic.PropositionalAxiomsTautology

open import Sets.FinSetWithK

open import Rings.Examples.Examples
open import Rings.Examples.Proofs

open import Groups.FreeGroup.UniversalProperty
open import Groups.FreeGroup.Parity
open import Groups.FreeProduct.Group
open import Groups.Examples.ExampleSheet1
open import Groups.LectureNotes.Lecture1

open import LectureNotes.NumbersAndSets.Lecture1
open import LectureNotes.Groups.Lecture1

open import ProjectEuler.Problem1

module Everything.WithK where
