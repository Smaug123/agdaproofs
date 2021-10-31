{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.ClassicalReals.RealField
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Fields
open import Groups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition

module Numbers.ClassicalReals.Examples (ℝ : RealField) where

open RealField ℝ
open Setoid S
open Equivalence eq
open Ring R
open Field F
open SetoidPartialOrder pOrder
open import Fields.Orders.LeastUpperBounds.Definition pOrder
open import Rings.Orders.Total.Lemmas orderedRing
open import Rings.Orders.Partial.Lemmas pOrderedRing
open Group additiveGroup
open PartiallyOrderedRing pOrderedRing
open SetoidTotalOrder (TotallyOrderedRing.total orderedRing)
open import Rings.InitialRing R
open import Fields.Orders.Lemmas oField
open import Rings.Lemmas R
open import Groups.Lemmas additiveGroup
open import Numbers.Intervals.Definition pOrderedRing
open import Numbers.Intervals.Arithmetic pOrderedRing
open import Fields.Lemmas F

squarePositive : (a : A) → (((a ∼ 0R) → False) && (0R < (a * a))) || (a ∼ 0R)
squarePositive a with totality 0R a
squarePositive a | inl (inl x) = inl ((λ a=0 → irreflexive (<WellDefined reflexive a=0 x)) ,, orderRespectsMultiplication x x)
squarePositive a | inl (inr x) = inl ((λ a=0 → irreflexive (<WellDefined a=0 reflexive x)) ,, <WellDefined reflexive twoNegativesTimes (orderRespectsMultiplication (<WellDefined invIdent reflexive (ringSwapNegatives' x)) (<WellDefined invIdent reflexive (ringSwapNegatives' x))))
squarePositive a | inr 0=a = inr (symmetric 0=a)

fraction<1 : (n m : ℕ) → n <N m → (0<m : fromN m ∼ 0G → False) → ((fromN n) * underlying (allInvertible (fromN m) 0<m)) < 1R
fraction<1 n m n<m 0<m with allInvertible (fromN m) 0<m
... | 1/m , prM = <WellDefined reflexive (transitive *Commutative prM) (ringCanMultiplyByPositive (inversePositiveIsPositive prM (fromNPreservesOrder (0<1 nontrivial) {0} {m} (zeroLeast n<m))) (fromNPreservesOrder (0<1 nontrivial) n<m))

1/2 : A
1/2 = underlying (allInvertible (1R + 1R) (orderedImpliesCharNot2 nontrivial))

pr1/2 : (1/2 * (1R + 1R)) ∼ 1R
pr1/2 with allInvertible (1R + 1R) (orderedImpliesCharNot2 nontrivial)
... | x , pr = pr

pr1/2' : (1/2 + 1/2) ∼ 1R
pr1/2' = transitive (symmetric (transitive *DistributesOver+ (+WellDefined (transitive *Commutative identIsIdent) (transitive *Commutative identIsIdent)))) pr1/2

1/2<1 : 1/2 < 1R
1/2<1 = <WellDefined (transitive (*WellDefined identRight (allInvertibleWellDefined (+WellDefined reflexive identRight))) identIsIdent) reflexive (fraction<1 1 2 (le 0 refl) λ p → charZero 1 (symmetric p))

3/2<2 : (fromN 3 * 1/2) < (1R + 1R)
3/2<2 = <WellDefined (transitive (+WellDefined reflexive (transitive (symmetric pr1/2) (transitive *Commutative (*WellDefined (+WellDefined reflexive (symmetric identRight)) reflexive)))) (symmetric *DistributesOver+')) reflexive (orderRespectsAddition (<WellDefined (symmetric identIsIdent) reflexive 1/2<1) 1R)

2<9/4 : (1R + 1R) < ((fromN 3 * 1/2) * (fromN 3 * 1/2))
2<9/4 = <WellDefined reflexive (symmetric *Associative) (halveInequality _ _ 1/2 pr1/2' (<WellDefined reflexive (transitive (symmetric *Associative) *Commutative) (halveInequality _ _ 1/2 pr1/2' (<WellDefined (transitive (fromNPreserves* 4 2) (transitive (*WellDefined (+WellDefined reflexive (+WellDefined reflexive (+WellDefined reflexive identRight))) (+WellDefined reflexive identRight)) (transitive *DistributesOver+ (+WellDefined (transitive *Commutative (transitive identIsIdent +Associative)) (transitive *Commutative (transitive identIsIdent +Associative)))))) (fromNPreserves* 3 3) (fromNPreservesOrder (0<1 nontrivial) (le {8} 0 refl))))))

0<2 : 0R < (1R + 1R)
0<2 = <WellDefined identLeft reflexive (ringAddInequalities (0<1 nontrivial) (0<1 nontrivial))

0<3/2 : 0R < (fromN 3 * 1/2)
0<3/2 = orderRespectsMultiplication (fromNPreservesOrder (0<1 nontrivial) (le {0} {3} 2 refl)) (inversePositiveIsPositive pr1/2 0<2)

3/2ub : {r : A} → (r * r) < (1R + 1R) → (r < (fromN 3 * 1/2))
3/2ub {r} r^2<2 with totality r (fromN 3 * 1/2)
3/2ub {r} r^2<2 | inl (inl r<3/2) = r<3/2
3/2ub {r} r^2<2 | inl (inr 3/2<r) = exFalso (irreflexive (<Transitive r^2<2 (<Transitive 2<9/4 (ringMultiplyPositives 0<3/2 0<3/2 3/2<r 3/2<r))))
3/2ub {r} r^2<2 | inr r=3/2 = exFalso (irreflexive (<Transitive r^2<2 (<WellDefined reflexive (symmetric (*WellDefined r=3/2 r=3/2)) 2<9/4)))

2/6<1 : ((1R + 1R) * underlying (allInvertible (fromN 6) (charZero' 5))) < 1R
2/6<1 with allInvertible (fromN 6) (charZero' 5)
2/6<1 | 1/6 , pr1/6 = <WellDefined reflexive (transitive *Commutative pr1/6) (ringCanMultiplyByPositive (inversePositiveIsPositive pr1/6 (fromNPreservesOrder (0<1 nontrivial) {0} {6} (le 5 refl))) (<WellDefined (+WellDefined reflexive identRight) reflexive (fromNPreservesOrder (0<1 nontrivial) {2} {6} (le 3 refl))))

2<2*2 : (1R + 1R) < ((1R + 1R) * (1R + 1R))
2<2*2 = (<WellDefined (+WellDefined reflexive identRight) (transitive (fromNPreserves* 2 2) (*WellDefined (+WellDefined reflexive identRight) (+WellDefined reflexive identRight))) (fromNPreservesOrder (0<1 nontrivial) {2} {4} (le 1 refl)))

square<2Means<2 : (u : A) → (u * u) < (1R + 1R) → u < (1R + 1R)
square<2Means<2 u u^2<2 with totality u (1R + 1R)
square<2Means<2 u u^2<2 | inl (inl x) = x
square<2Means<2 u u^2<2 | inl (inr x) = exFalso (irreflexive (<Transitive u^2<2 (<Transitive 2<2*2 (ringMultiplyPositives 0<2 0<2 x x))))
square<2Means<2 u u^2<2 | inr u=2 = exFalso (irreflexive (<Transitive (<WellDefined (*WellDefined u=2 u=2) reflexive u^2<2) 2<2*2))

2=2*2-2 : (fromN 2) ∼ (((1R + 1R) * (1R + 1R)) + inverse (fromN 2))
2=2*2-2 = transitive (+WellDefined reflexive identRight) (transitive (transitive (transitive (transitive (symmetric identRight) (+WellDefined reflexive (symmetric invRight))) +Associative) (+WellDefined (symmetric (+WellDefined (+WellDefined identIsIdent identIsIdent) (+WellDefined identIsIdent identIsIdent))) reflexive)) (+WellDefined (transitive (+WellDefined (symmetric *DistributesOver+') (symmetric *DistributesOver+')) (symmetric *DistributesOver+)) (inverseWellDefined (symmetric (+WellDefined reflexive identRight)))))

sqrtRespectsInequality : {x y : A} → (x * x) < (y * y) → 0R < y → x < y
sqrtRespectsInequality {x} {y} x^2<y^2 _ with totality x y
sqrtRespectsInequality {x} {y} x^2<y^2 _ | inl (inl x<y) = x<y
sqrtRespectsInequality {x} {y} x^2<y^2 0<y | inl (inr y<x) = exFalso (irreflexive (<Transitive x^2<y^2 (ringMultiplyPositives 0<y 0<y y<x y<x)))
sqrtRespectsInequality {x} {y} x^2<y^2 _ | inr x=y = exFalso (irreflexive (<WellDefined (*WellDefined x=y x=y) reflexive x^2<y^2))

sqrt2 : Sg A (λ i → (i * i) ∼ (1R + 1R))
sqrt2 = sqrt2' , sqrt2IsSqrt2
  where
    pred : A → Set c
    pred a = (a * a) < (1R + 1R)
    sub : subset S pred
    sub {y} x=y x^2<2 = <WellDefined (*WellDefined x=y x=y) reflexive x^2<2
    abstract
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
    sqrt2IsSqrt2 | inl (inl sup^2<2) | sqrt2' , record { upperBound = upperBound ; leastUpperBound = leastUpperBound } = exFalso bad
      where
        abstract
          t : A
          t = ((fromN 2) + inverse (sqrt2' * sqrt2')) * (underlying (allInvertible (fromN 6) (charZero' 5)))
          pr' : (underlying (allInvertible (fromN 6) (charZero' 5)) * fromN 6) ∼ 1R
          pr' with allInvertible (fromN 6) (charZero' 5)
          ... | x , p = p
          crudeBound : isInInterval (sqrt2' * sqrt2') record { minBound = 0R ; maxBound = 1R + 1R }
          crudeBound with squarePositive sqrt2'
          crudeBound | inl (_ ,, snd) = snd ,, sup^2<2
          crudeBound | inr sqrt2=0 with upperBound 1R (<WellDefined (transitive identRight (symmetric identIsIdent)) (+WellDefined reflexive identRight) (fromNPreservesOrder (0<1 nontrivial) {1} {2} (le 0 refl)))
          crudeBound | inr sqrt2=0 | inl 1<sqrt2 = exFalso (irreflexive (<Transitive 1<sqrt2 (<WellDefined (symmetric sqrt2=0) reflexive (0<1 nontrivial))))
          crudeBound | inr sqrt2=0 | inr 1=sqrt2 = exFalso (nontrivial (transitive (symmetric sqrt2=0) (symmetric 1=sqrt2)))
          crudeBound' : isInInterval (inverse (sqrt2' * sqrt2')) record { minBound = inverse (1R + 1R) ; maxBound = inverse 0R }
          crudeBound' = intervalInverseContains crudeBound
          numeratorBound : isInInterval (inverse (sqrt2' * sqrt2') + fromN 2) record { minBound = 0R ; maxBound = 1R + 1R }
          numeratorBound = intervalWellDefined (transitive groupIsAbelian (transferToRight'' (transitive +Associative identRight)) ,, transitive (+WellDefined invIdent reflexive) (transitive identLeft (+WellDefined reflexive identRight))) (intervalConstantSumContains (fromN 2) crudeBound')
          numeratorBound' : isInInterval (fromN 2 + inverse (sqrt2' * sqrt2')) record { minBound = 0R ; maxBound = 1R + 1R }
          numeratorBound' = intervalWellDefined' groupIsAbelian numeratorBound
          tBound : isInInterval t record { minBound = 0R ; maxBound = (1R + 1R) * (underlying (allInvertible (fromN 6) (charZero' 5))) }
          tBound = intervalWellDefined (transitive *Commutative timesZero ,, reflexive) (intervalConstantProductContains (inversePositiveIsPositive pr' (fromNPreservesOrder (0<1 nontrivial) {0} {6} (le 5 refl))) numeratorBound')
          u : ((((fromN 5) * ((fromN 2) + inverse (sqrt2' * sqrt2'))) * underlying (allInvertible (fromN 6) (charZero' 5))) + (sqrt2' * sqrt2')) < ((fromN 2 + inverse (sqrt2' * sqrt2')) + (sqrt2' * sqrt2'))
          u = orderRespectsAddition (<WellDefined (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) identIsIdent (ringCanMultiplyByPositive {(fromN 5) * underlying (allInvertible (fromN 6) (charZero' 5))} {1R} {fromN 2 + inverse (sqrt2' * sqrt2')} (moveInequality (<WellDefined reflexive (transitive (symmetric identRight) (symmetric +Associative)) sup^2<2)) (fraction<1 5 6 (le zero refl) λ pr → charZero' 5 pr))) (sqrt2' * sqrt2')
          tBound' : (((fromN 5) * t) + (sqrt2' * sqrt2')) < (1R + 1R)
          tBound' = <WellDefined (+WellDefined (symmetric *Associative) reflexive) (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) (transitive identRight (+WellDefined reflexive identRight)))) u
          sqrt2<2 : sqrt2' < (1R + 1R)
          sqrt2<2 with leastUpperBound (fromN 3 * 1/2) (λ r s → inl (3/2ub s))
          sqrt2<2 | inl x = <Transitive x 3/2<2
          sqrt2<2 | inr x = <WellDefined (symmetric x) reflexive 3/2<2
          2sqrt2<4 : (sqrt2' + sqrt2') < fromN 4
          2sqrt2<4 = <WellDefined (transitive *DistributesOver+ (+WellDefined (transitive *Commutative identIsIdent) (transitive *Commutative identIsIdent))) (transitive (transitive (*WellDefined (symmetric identRight) (symmetric identRight)) (*WellDefined (symmetric +Associative) (symmetric +Associative))) (symmetric (fromNPreserves* 2 2))) (ringCanMultiplyByPositive {sqrt2'} {1R + 1R} {1R + 1R} (<WellDefined identLeft reflexive (ringAddInequalities (0<1 nontrivial) (0<1 nontrivial))) sqrt2<2)
          t<1 : t < 1R
          t<1 = <Transitive (_&&_.snd tBound) 2/6<1
          newElementIsElement : ((sqrt2' + t) * (sqrt2' + t)) < (1R + 1R)
          newElementIsElement = <WellDefined (symmetric *DistributesOver+') reflexive (<WellDefined (+WellDefined (symmetric *DistributesOver+) reflexive) reflexive (<WellDefined (transitive groupIsAbelian +Associative) reflexive (<Transitive (orderRespectsAddition (<WellDefined (+WellDefined *Commutative reflexive) reflexive (<WellDefined (transitive *Commutative *DistributesOver+) reflexive (ringCanMultiplyByPositive (_&&_.fst tBound) (<WellDefined (symmetric +Associative) reflexive (<Transitive (orderRespectsAddition 2sqrt2<4 t) (<WellDefined groupIsAbelian reflexive (<WellDefined reflexive (reflexive {fromN 5}) (orderRespectsAddition t<1 (fromN 4))))))))) (sqrt2' * sqrt2')) tBound')))
        bad : False
        bad with upperBound (sqrt2' + t) newElementIsElement
        bad | inl x = irreflexive (<Transitive x (<WellDefined identLeft groupIsAbelian (orderRespectsAddition (_&&_.fst tBound) sqrt2')))
        bad | inr x = irreflexive (<WellDefined identLeft (transitive groupIsAbelian x) (orderRespectsAddition (_&&_.fst tBound) sqrt2'))
    sqrt2IsSqrt2 | inl (inr 2<sup^2) with sup
    sqrt2IsSqrt2 | inl (inr 2<sup^2) | sqrt2' , record { upperBound = upperBound ; leastUpperBound = leastUpperBound } = exFalso bad
      where
        abstract
          1<sqrt2 : 1R < sqrt2'
          1<sqrt2 with upperBound 1R (<WellDefined (transitive identRight (symmetric identIsIdent)) (+WellDefined reflexive identRight) (fromNPreservesOrder (0<1 nontrivial) {1} {2} (le zero refl)))
          1<sqrt2 | inl x = x
          1<sqrt2 | inr x = exFalso (irreflexive (<Transitive 2<sup^2 (<WellDefined (transitive identRight (transitive (symmetric identIsIdent) (*WellDefined x x))) (+WellDefined reflexive identRight) (fromNPreservesOrder (0<1 nontrivial) {1} {2} (le 0 refl)))))
          0<sqrt2 : 0R < sqrt2'
          0<sqrt2 = <Transitive (0<1 nontrivial) 1<sqrt2
          sqrt2<2 : sqrt2' < (1R + 1R)
          sqrt2<2 with leastUpperBound (fromN 3 * 1/2) (λ r s → inl (3/2ub s))
          sqrt2<2 | inl x = <Transitive x 3/2<2
          sqrt2<2 | inr x = <WellDefined (symmetric x) reflexive 3/2<2
          2sqrt2<4 : (sqrt2' + sqrt2') < fromN 4
          2sqrt2<4 = <WellDefined (transitive *DistributesOver+ (+WellDefined (transitive *Commutative identIsIdent) (transitive *Commutative identIsIdent))) (transitive (transitive (*WellDefined (symmetric identRight) (symmetric identRight)) (*WellDefined (symmetric +Associative) (symmetric +Associative))) (symmetric (fromNPreserves* 2 2))) (ringCanMultiplyByPositive {sqrt2'} {1R + 1R} {1R + 1R} (<WellDefined identLeft reflexive (ringAddInequalities (0<1 nontrivial) (0<1 nontrivial))) sqrt2<2)
          t : A
          t = ((sqrt2' * sqrt2') + inverse (fromN 2)) * underlying (allInvertible (fromN 4) (charZero' 3))
          pr1 : inverse (fromN 4 * t) ∼ (inverse (sqrt2' * sqrt2') + (fromN 2))
          pr1 with allInvertible (fromN 4) (charZero' 3)
          ... | 1/4 , pr1/4 = transitive (transitive (transitive (transitive (symmetric ringMinusExtracts) (transitive (transitive (*WellDefined reflexive (transitive (symmetric ringMinusExtracts') (transitive *Commutative (*WellDefined reflexive (transitive invContravariant (transitive groupIsAbelian (+WellDefined reflexive invInv))))))) *Associative) *Commutative)) (*WellDefined reflexive (transitive *Commutative pr1/4))) *Commutative) identIsIdent
          t<sqrt2 : t < sqrt2'
          t<sqrt2 with allInvertible (fromN 4) (charZero' 3)
          ... | 1/4 , pr4 = <WellDefined reflexive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive (transitive *Commutative pr4)) (transitive *Commutative identIsIdent))) (ringCanMultiplyByPositive (inversePositiveIsPositive pr4 (fromNPreservesOrder (0<1 nontrivial) {0} {4} (le 3 refl))) (<Transitive (orderRespectsAddition (ringMultiplyPositives 0<sqrt2 0<sqrt2 sqrt2<2 sqrt2<2) (inverse (1R + (1R + 0G)))) (<WellDefined {fromN 2} 2=2*2-2 reflexive (<Transitive {fromN 2} {sqrt2' * fromN 2} (<WellDefined identIsIdent reflexive (ringCanMultiplyByPositive (fromNPreservesOrder (0<1 nontrivial) {0} (le 1 refl)) 1<sqrt2)) (<WellDefined *Commutative *Commutative (ringCanMultiplyByPositive 0<sqrt2 (fromNPreservesOrder (0<1 nontrivial) {2} (le 1 refl))))))))
          0<t : 0R < t
          0<t with allInvertible (fromN 4) (charZero' 3)
          ... | 1/4 , pr4 = orderRespectsMultiplication (<WellDefined reflexive (+WellDefined reflexive (inverseWellDefined (+WellDefined reflexive (symmetric identRight)))) (moveInequality 2<sup^2)) (inversePositiveIsPositive pr4 (fromNPreservesOrder (0<1 nontrivial) {0} {4} (le 3 refl)))
        anotherUpperBound : A
        anotherUpperBound = (sqrt2' + inverse t) * (sqrt2' + inverse t)
        abstract
          u : anotherUpperBound ∼ ((sqrt2' * sqrt2') + (inverse ((t * sqrt2') + (t * sqrt2')) + (t * t)))
          u = transitive *DistributesOver+' (transitive (+WellDefined *DistributesOver+ reflexive) (transitive (symmetric +Associative) (+WellDefined reflexive (transitive (+WellDefined ringMinusExtracts *DistributesOver+) (transitive +Associative (+WellDefined (transitive (+WellDefined (inverseWellDefined *Commutative) ringMinusExtracts') (symmetric invContravariant)) twoNegativesTimes))))))
          w : ((sqrt2' * sqrt2') + inverse ((fromN 4) * t)) < anotherUpperBound
          w = <WellDefined reflexive (symmetric u) (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (<WellDefined (ringMinusExtracts') (+WellDefined (inverseWellDefined (*DistributesOver+)) reflexive) (<WellDefined reflexive (+WellDefined ringMinusExtracts reflexive) (<WellDefined reflexive *DistributesOver+ (<WellDefined reflexive *Commutative (ringCanMultiplyByPositive 0<t (<WellDefined identRight reflexive (ringAddInequalities (ringSwapNegatives' (<WellDefined reflexive (transitive (+WellDefined (+WellDefined reflexive (symmetric identRight)) (+WellDefined reflexive (symmetric identRight))) (symmetric (fromNPreserves+ 2 2))) (ringAddInequalities sqrt2<2 sqrt2<2))) 0<t))))))) (sqrt2' * sqrt2')))
          w' : ((sqrt2' * sqrt2') + inverse ((fromN 4) * t)) ∼ (1R + 1R)
          w' = transitive (+WellDefined reflexive pr1) (transitive +Associative (transitive (+WellDefined invRight reflexive) (transitive identLeft (+WellDefined reflexive identRight))))
          anotherUpperBoundBounds : (1R + 1R) < anotherUpperBound
          anotherUpperBoundBounds = <WellDefined w' reflexive w
        aubIsBound : UpperBound sub (sqrt2' + inverse t)
        aubIsBound y y^2<2 with totality y (sqrt2' + inverse t)
        aubIsBound y y^2<2 | inl (inl x) = inl x
        aubIsBound y y^2<2 | inl (inr x) = exFalso (irreflexive (<Transitive (<Transitive anotherUpperBoundBounds (ringMultiplyPositives (moveInequality t<sqrt2) (moveInequality t<sqrt2) x x)) y^2<2))
        aubIsBound y y^2<2 | inr x = inr x
        bad : False
        bad with leastUpperBound (sqrt2' + inverse t) aubIsBound
        bad | inl x = irreflexive (<Transitive x (<WellDefined groupIsAbelian identLeft (orderRespectsAddition (ringMinusFlipsOrder 0<t) sqrt2')))
        bad | inr x = irreflexive (<WellDefined (symmetric (transitive x groupIsAbelian)) identLeft (orderRespectsAddition (ringMinusFlipsOrder 0<t) sqrt2'))
    sqrt2IsSqrt2 | inr x = x
