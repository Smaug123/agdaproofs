{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.Naturals.Naturals
open import Numbers.Integers.Definition
open import Numbers.Integers.Addition
open import Numbers.Integers.Multiplication
open import Numbers.Integers.Order
open import Groups.Definition

module Numbers.Integers.Integers where

open Numbers.Integers.Definition using (ℤ ; nonneg ; negSucc) public
open Numbers.Integers.Addition using (_+Z_ ; ℤGroup ; ℤAbGrp) public
open Numbers.Integers.Multiplication using (_*Z_ ; ℤIntDom ; ℤRing) public
open Numbers.Integers.Order using (_<Z_ ; ℤOrderedRing) public

_-Z_ : ℤ → ℤ → ℤ
a -Z b = a +Z (Group.inverse ℤGroup b)

_^Z_ : ℤ → ℕ → ℤ
a ^Z zero = nonneg 1
a ^Z succ b = a *Z (a ^Z b)
