{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.ClassicalReals.RealField
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Sets.EquivalenceRelations
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Fields
open import Groups.Definition

module Numbers.ClassicalReals.Examples (ℝ : RealField) where

open RealField ℝ
open Setoid S
open Equivalence eq
open Ring R
open SetoidPartialOrder pOrder
open import Fields.Orders.LeastUpperBounds.Definition pOrder
open import Rings.Orders.Total.Lemmas orderedRing
open import Rings.Orders.Partial.Lemmas pOrderedRing
open Group additiveGroup
open PartiallyOrderedRing pOrderedRing
open SetoidTotalOrder (TotallyOrderedRing.total orderedRing)

sqrt2 : Sg A (λ i → (i * i) ∼ (1R + 1R))
sqrt2 = sqrt2' , sqrt2IsSqrt2
  where
    pred : A → Set c
    pred a = (a * a) < (1R + 1R)
    sub : subset S pred
    sub {y} x=y x^2<2 = <WellDefined (*WellDefined x=y x=y) reflexive x^2<2
    abstract
      0<2 : 0R < (1R + 1R)
      0<2 = <WellDefined identLeft reflexive (ringAddInequalities (0<1 nontrivial) (0<1 nontrivial))
      2ub : UpperBound sub (1R + 1R)
      2ub y y^2<2 with totality y (1R + 1R)
      2ub y y^2<2 | inl (inl y<2) = inl y<2
      2ub y y^2<2 | inl (inr 2<y) = exFalso (irreflexive (<Transitive y^2<2 (<Transitive s r)))
        where
          r : ((1R + 1R) * (1R + 1R)) < (y * y)
          r = ringMultiplyPositives 0<2 0<2 2<y 2<y
          s : (1R + 1R) < ((1R + 1R) * (1R + 1R))
          s = <WellDefined reflexive (symmetric *DistributesOver+) (<WellDefined reflexive (+WellDefined (transitive (symmetric identIsIdent) *Commutative) (transitive (symmetric identIsIdent) *Commutative)) (<WellDefined identLeft reflexive (orderRespectsAddition 0<2 (1R + 1R))))
      2ub y y^2<2 | inr y=2 = inr y=2
    abstract
      sup : Sg A (LeastUpperBound sub)
      sup = lub sub (0R , <Transitive (<WellDefined (symmetric timesZero) (symmetric identLeft) (0<1 nontrivial)) (orderRespectsAddition (0<1 nontrivial) 1R)) ((1R + 1R) , 2ub)
    sqrt2' : A
    sqrt2' = underlying sup
    sqrt2IsSqrt2 : (sqrt2' * sqrt2') ∼ (1R + 1R)
    sqrt2IsSqrt2 with totality (sqrt2' * sqrt2') (1R + 1R)
    sqrt2IsSqrt2 | inl (inl sup^2<2) with sup
    sqrt2IsSqrt2 | inl (inl sup^2<2) | sqrt2' , record { upperBound = upperBound ; leastUpperBound = leastUpperBound } = exFalso {!!}
    sqrt2IsSqrt2 | inl (inr 2<sup^2) with sup
    sqrt2IsSqrt2 | inl (inr 2<sup^2) | sqrt2' , record { upperBound = upperBound ; leastUpperBound = leastUpperBound } = exFalso {!!}
    sqrt2IsSqrt2 | inr x = x
