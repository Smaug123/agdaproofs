{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Groups
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Setoids.Functions.Extension

module Groups.SymmetricGroups.CycleType where

