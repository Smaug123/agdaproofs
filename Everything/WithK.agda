{-# OPTIONS --warning=error --safe #-}

-- This file contains everything that is --safe, but uses K.

open import PrimeNumbers
open import Numbers.Integers
open import Numbers.Rationals
open import Numbers.RationalsLemmas
open import Numbers.BinaryNaturals.Multiplication -- TODO there's no reason for this to need K
open import Numbers.BinaryNaturals.Order -- TODO likewise this

open import Logic.PropositionalLogic
open import Logic.PropositionalLogicExamples
open import Logic.PropositionalAxiomsTautology

open import IntegersModN

open import Sets.FinSetWithK

open import Vectors

open import KeyValue
open import KeyValueWithDomain

open import Rings.Examples.Examples
open import Rings.Examples.Proofs

open import Groups.FreeGroups
open import Groups.Groups2
open import Groups.Examples.ExampleSheet1
open import Groups.LectureNotes.Lecture1

module Everything.WithK where
