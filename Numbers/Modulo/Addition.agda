{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition
open import Numbers.Modulo.Definition

module Numbers.Modulo.Addition where

_+n_ : {n : ℕ} {pr : 0 <N n} → ℤn n pr → ℤn n pr → ℤn n pr
fzero +n b = b
fsucc a +n b = ?
