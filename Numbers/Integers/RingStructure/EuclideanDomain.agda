{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Multiplication
open import Numbers.Integers.RingStructure.Ring
open import Numbers.Integers.RingStructure.IntegralDomain
open import Semirings.Definition
open import Groups.Definition
open import Rings.Definition
open import Setoids.Setoids
open import Rings.EuclideanDomains.Definition

module Numbers.Integers.RingStructure.EuclideanDomain where

ℤEuclideanDomain : EuclideanDomain ℤRing
EuclideanDomain.isIntegralDomain ℤEuclideanDomain = ℤIntDom
EuclideanDomain.norm ℤEuclideanDomain {nonneg x} a!=0 = x
EuclideanDomain.norm ℤEuclideanDomain {negSucc x} a!=0 = succ x
EuclideanDomain.normSize ℤEuclideanDomain {nonneg a} {nonneg b} a!=0 b!=0 (nonneg 0) b=ac rewrite nonnegInjective b=ac | multiplicationNIsCommutative a 0 = exFalso ((b!=0 refl))
EuclideanDomain.normSize ℤEuclideanDomain {nonneg a} {nonneg b} a!=0 b!=0 (nonneg (succ 0)) b=ac rewrite nonnegInjective b=ac | multiplicationNIsCommutative a 1 = inr (equalityCommutative (Semiring.sumZeroRight ℕSemiring a))
EuclideanDomain.normSize ℤEuclideanDomain {nonneg 0} {nonneg b} a!=0 b!=0 (nonneg (succ (succ c))) b=ac = exFalso (a!=0 refl)
EuclideanDomain.normSize ℤEuclideanDomain {nonneg (succ a)} {nonneg b} a!=0 b!=0 (nonneg (succ (succ c))) b=ac rewrite nonnegInjective b=ac = inl {!!}
EuclideanDomain.normSize ℤEuclideanDomain {nonneg a} {nonneg b} a!=0 b!=0 (negSucc c) b=ac = exFalso {!!}
EuclideanDomain.normSize ℤEuclideanDomain {nonneg a} {negSucc b} a!=0 b!=0 c b=ac = {!!}
EuclideanDomain.normSize ℤEuclideanDomain {negSucc a} {b} a!=0 b!=0 c b=ac = {!!}
EuclideanDomain.divisionAlg ℤEuclideanDomain = {!!}
