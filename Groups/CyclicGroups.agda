{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Integers
open import Numbers.Integers.Addition
open import Sets.FinSet
open import Groups.Homomorphisms.Definition
open import Groups.Groups
open import Groups.Subgroups.Definition
open import Groups.Abelian.Definition
open import Groups.Definition

module Groups.CyclicGroups {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) where

