{-# OPTIONS --safe --warning=error #-}
-- These are explicitly with-K, because we currently encode an element of Zn as
-- a natural together with a proof that it is small.

open import LogicalFormulae
open import Groups.Definition
open import Groups.Groups
open import Groups.Abelian.Definition
open import Groups.FiniteGroups.Definition
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Addition -- TODO remove this dependency
open import Numbers.Primes.PrimeNumbers
open import Setoids.Setoids
open import Sets.FinSet
open import Sets.FinSetWithK
open import Functions
open import Numbers.Naturals.WithK
open import Semirings.Definition
open import Orders

module Numbers.Modulo.Definition where
  record ℤn (n : ℕ) (pr : 0 <N n) : Set where
    field
      x : ℕ
      xLess : x <N n

  equalityZn : {n : ℕ} {pr : 0 <N n} → (a b : ℤn n pr) → (ℤn.x a ≡ ℤn.x b) → a ≡ b
  equalityZn record { x = a ; xLess = aLess } record { x = .a ; xLess = bLess } refl rewrite <NRefl aLess bLess = refl
