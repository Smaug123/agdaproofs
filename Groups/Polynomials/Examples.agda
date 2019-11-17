{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Numbers.Integers.Integers
open import Numbers.Integers.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Vectors
open import Lists.Lists
open import Maybe

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Polynomials.Examples where

open import Groups.Polynomials.Definition ℤGroup

private
  decide : _
  decide = (λ a → ℤDecideEquality a (nonneg 0))

  p1 : degree decide [] ≡ no
  p1 = refl

  p2 : degree decide (nonneg 0 :: []) ≡ no
  p2 = refl

  p3 : degree decide (nonneg 1 :: []) ≡ yes 0
  p3 = refl
