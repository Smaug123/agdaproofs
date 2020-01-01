{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Groups.Groups
open import Groups.Abelian.Definition
open import Groups.FiniteGroups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Setoids.Setoids
open import Sets.FinSet.Definition
open import Functions
open import Semirings.Definition
open import Numbers.Naturals.EuclideanAlgorithm
open import Orders.Total.Definition

module Numbers.Modulo.Definition where

record ℤn (n : ℕ) .(pr : 0 <N n) : Set where
  field
    x : ℕ
    .xLess : x <N n

equalityZn : {n : ℕ} .{pr : 0 <N n} → {a b : ℤn n pr} → (ℤn.x a ≡ ℤn.x b) → a ≡ b
equalityZn {a = record { x = a ; xLess = aLess }} {record { x = .a ; xLess = bLess }} refl = refl

