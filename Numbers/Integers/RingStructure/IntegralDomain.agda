{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Multiplication
open import Numbers.Integers.RingStructure.Ring
open import Semirings.Definition
open import Groups.Definition
open import Rings.Definition
open import Setoids.Setoids
open import Rings.IntegralDomains

module Numbers.Integers.RingStructure.IntegralDomain where

intDom : (a b : ℤ) → a *Z b ≡ nonneg 0 → (a ≡ nonneg 0) || (b ≡ nonneg 0)
intDom (nonneg zero) (nonneg b) pr = inl refl
intDom (nonneg (succ a)) (nonneg zero) pr = inr refl
intDom (nonneg zero) (negSucc b) pr = inl refl
intDom (negSucc a) (nonneg zero) pr = inr refl

ℤIntDom : IntegralDomain ℤRing
IntegralDomain.intDom ℤIntDom {a} {b} = intDom a b
IntegralDomain.nontrivial ℤIntDom ()
