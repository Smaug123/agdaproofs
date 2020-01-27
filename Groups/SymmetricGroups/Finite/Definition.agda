{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Sets.FinSet
open import Groups.Groups
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Setoids.Functions.Extension
open import Groups.SymmetricGroups.Definition

module Groups.SymmetricGroups.Finite.Definition where

snSet : (n : ℕ) → Set
snSet n = SymmetryGroupElements (reflSetoid (FinSet n))

snSetoid : (n : ℕ) → Setoid (snSet n)
snSetoid n = symmetricSetoid (reflSetoid (FinSet n))

SymmetricGroupN : (n : ℕ) → Group (snSetoid n) (symmetricGroupOp)
SymmetricGroupN n = symmetricGroup (reflSetoid (FinSet n))

record Cycles {n : ℕ} (s : snSet n) : Set where
  field
    

cycles : {n : ℕ} → (s : snSet n) → Cycles s
cycles s = {!!}
