{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Total.Lemmas
open import Rings.IntegralDomains.Definition
open import Functions
open import Setoids.Setoids
open import Setoids.Orders
open import Sets.EquivalenceRelations


module Fields.FieldOfFractions.Order {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {pRing : PartiallyOrderedRing R pOrder} (I : IntegralDomain R) (order : TotallyOrderedRing pRing) where

open import Fields.FieldOfFractions.Setoid I
open import Fields.FieldOfFractions.Ring I

open SetoidTotalOrder (TotallyOrderedRing.total order)
open import Rings.Orders.Partial.Lemmas
open PartiallyOrderedRing pRing

fieldOfFractionsComparison : Rel fieldOfFractionsSet
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) with totality (Ring.0R R) denomA
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) with totality (Ring.0R R) denomB
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) = (numA * denomB) < (numB * denomA)
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) = (numB * denomA) < (numA * denomB)
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inr 0=denomB = exFalso (denomB!=0 (symmetric 0=denomB))
  where
    open Equivalence (Setoid.eq S)
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) with totality (Ring.0R R) denomB
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) = (numB * denomA) < (numA * denomB)
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) = (numA * denomB) < (numB * denomA)
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inr 0=denomB = exFalso (denomB!=0 (symmetric 0=denomB))
  where
    open Equivalence (Setoid.eq S)
fieldOfFractionsComparison (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inr 0=denomA = exFalso (denomA!=0 (symmetric 0=denomA))
  where
    open Equivalence (Setoid.eq S)

fieldOfFractionsOrderWellDefinedLeft : {x y z : fieldOfFractionsSet} → fieldOfFractionsComparison x y → Setoid._∼_ fieldOfFractionsSetoid x z → fieldOfFractionsComparison z y
fieldOfFractionsOrderWellDefinedLeft {(numX ,, (denomX , denomX!=0))} {(numY ,, (denomY , denomY!=0))} {(numZ ,, (denomZ , denomZ!=0))} x<y x=z with totality (Ring.0R R) denomZ
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) with totality (Ring.0R R) denomX
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inl _) = s
  where
    open Ring R
    open Equivalence (Setoid.eq S)
    have : ((numX * denomY) * denomZ) < ((numY * denomX) * denomZ)
    have = ringCanMultiplyByPositive pRing 0<denomZ x<y
    p : ((numX * denomZ) * denomY) < ((numY * denomX) * denomZ)
    p = SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) reflexive have
    q : ((denomX * numZ) * denomY) < ((numY * denomX) * denomZ)
    q = SetoidPartialOrder.<WellDefined pOrder (*WellDefined x=z reflexive) reflexive p
    r : ((numZ * denomY) * denomX) < ((numY * denomZ) * denomX)
    r = SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) *Commutative) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) q
    s : (numZ * denomY) < (numY * denomZ)
    s = ringCanCancelPositive order 0<denomX r
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inr x) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomY x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (symmetric x))
  where
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inl _) = ringCanCancelNegative order denomX<0 r
  where
    open Ring R
    open Equivalence (Setoid.eq S)
    p : ((numY * denomX) * denomZ) < ((numX * denomZ) * denomY)
    p = SetoidPartialOrder.<WellDefined pOrder reflexive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByPositive pRing 0<denomZ x<y)
    q : ((numY * denomX) * denomZ) < ((denomX * numZ) * denomY)
    q = SetoidPartialOrder.<WellDefined pOrder reflexive (*WellDefined x=z reflexive) p
    r : ((numY * denomZ) * denomX) < ((numZ * denomY) * denomX)
    r = SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) *Commutative) q
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inr x) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomY x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inr 0=denomX = exFalso (denomX!=0 (Equivalence.symmetric (Setoid.eq S) 0=denomX))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) with totality (Ring.0R R) denomX
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomY denomY<0))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inr _) = ringCanCancelPositive order 0<denomX r
  where
    open Ring R
    open Equivalence (Setoid.eq S)
    p : ((numY * denomX) * denomZ) < ((numX * denomY) * denomZ)
    p = ringCanMultiplyByPositive pRing 0<denomZ x<y
    q : ((numY * denomX) * denomZ) < ((denomX * numZ) * denomY)
    q = SetoidPartialOrder.<WellDefined pOrder reflexive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (*WellDefined x=z reflexive)))) p
    r : ((numY * denomZ) * denomX) < ((numZ * denomY) * denomX)
    r = SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) *Commutative) q
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomY denomY<0))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inr _) = ringCanCancelNegative order denomX<0 q
  where
    open Ring R
    open Equivalence (Setoid.eq S)
    p : ((numX * denomY) * denomZ) < ((numY * denomX) * denomZ)
    p = ringCanMultiplyByPositive pRing 0<denomZ x<y
    q : ((numZ * denomY) * denomX) < ((numY * denomZ) * denomX)
    q = SetoidPartialOrder.<WellDefined pOrder (transitive (*WellDefined *Commutative reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive x=z) (transitive *Commutative (transitive (symmetric *Associative) *Commutative))))) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) p
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inr 0=denomX = exFalso (denomX!=0 (Equivalence.symmetric (Setoid.eq S) 0=denomX))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inr 0=denomY = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) 0=denomY))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) with totality (Ring.0R R) denomX
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inl _) = ringCanCancelPositive order 0<denomX (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive x=z) (transitive (*WellDefined reflexive (*Commutative)) (transitive *Associative (*WellDefined *Commutative reflexive))))) p)
  where
    open Ring R
    open Equivalence (Setoid.eq S)
    p : ((numY * denomX) * denomZ) < ((denomY * numX) * denomZ)
    p = ringCanMultiplyByNegative pRing denomZ<0 (SetoidPartialOrder.<WellDefined pOrder *Commutative reflexive x<y)
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inr denomY<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomY denomY<0))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inl _) = ringCanCancelNegative order denomX<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined x=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) p)
  where
    open Ring R
    open Equivalence (Setoid.eq S)
    p : ((numX * denomY) * denomZ) < ((numY * denomX) * denomZ)
    p = ringCanMultiplyByNegative pRing denomZ<0 x<y
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inr denomY<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder denomY<0 0<denomY))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) | inr 0=denomY = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) 0=denomY))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inr x = exFalso (denomX!=0 (symmetric x))
  where
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) with totality (Ring.0R R) denomX
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomY denomY<0))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inr _) = ringCanCancelPositive order 0<denomX (SetoidPartialOrder.<WellDefined pOrder (transitive (*WellDefined *Commutative reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive x=z) (transitive *Associative (transitive *Commutative *Associative))))) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByNegative pRing denomZ<0 x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomY denomY<0))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inr _) = ringCanCancelNegative order denomX<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (*WellDefined *Commutative reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive x=z) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (*WellDefined *Commutative reflexive)))))) (ringCanMultiplyByNegative pRing denomZ<0 x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inr x = exFalso (denomX!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inr x = exFalso (denomY!=0 (symmetric x))
  where
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedLeft {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inr 0=denomZ = exFalso (denomZ!=0 (symmetric 0=denomZ))
  where
    open Equivalence (Setoid.eq S)

fieldOfFractionsOrderWellDefinedRight : {x y z : fieldOfFractionsSet} → fieldOfFractionsComparison x y → Setoid._∼_ (fieldOfFractionsSetoid) y z → fieldOfFractionsComparison x z
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z with totality (Ring.0R R) denomX
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) with totality (Ring.0R R) denomZ
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (ringCanMultiplyByPositive pRing 0<denomZ x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByPositive pRing 0<denomZ x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByNegative pRing denomZ<0 x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive (*Associative) (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (ringCanMultiplyByNegative pRing denomZ<0 x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inr x = exFalso (denomZ!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) with totality (Ring.0R R) denomZ
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByPositive pRing 0<denomZ x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (ringCanMultiplyByPositive pRing 0<denomZ x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) with totality (Ring.0R R) denomY
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (ringCanMultiplyByNegative pRing denomZ<0 x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined y=z reflexive) (transitive (symmetric *Associative) *Commutative))))) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByNegative pRing denomZ<0 x<y))
  where
    open Ring R
    open Equivalence (Setoid.eq S)
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) | inr x = exFalso (denomY!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inr x = exFalso (denomZ!=0 (Equivalence.symmetric (Setoid.eq S) x))
fieldOfFractionsOrderWellDefinedRight {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inr x = exFalso (denomX!=0 (Equivalence.symmetric (Setoid.eq S) x))

swapLemma : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) {x y z : A} → Setoid._∼_ S ((x * y) * z) ((x * z) * y)
swapLemma {S = S} R = transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)

fieldOfFractionsOrder : SetoidPartialOrder fieldOfFractionsSetoid fieldOfFractionsComparison
SetoidPartialOrder.<WellDefined (fieldOfFractionsOrder) {a} {b} {c} {d} a=b c=d a<c = fieldOfFractionsOrderWellDefinedRight {b} {c} {d} (fieldOfFractionsOrderWellDefinedLeft {a} {c} {b} a<c a=b) c=d
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr with totality (Ring.0R R) aDenom
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) with totality (Ring.0R R) aDenom
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) | inl (inl _) = SetoidPartialOrder.irreflexive pOrder pr
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) | inl (inr aDenom<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<aDenom aDenom<0))
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) | inr x = exFalso (aDenom!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) with totality (Ring.0R R) aDenom
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) | inl (inl 0<aDenom) = SetoidPartialOrder.irreflexive pOrder pr
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) | inl (inr _) = SetoidPartialOrder.irreflexive pOrder pr
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) | inr x = exFalso (aDenom!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.irreflexive (fieldOfFractionsOrder) {aNum ,, (aDenom , aDenom!=0)} pr | inr x = exFalso (aDenom!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c with totality (Ring.0R R) denomA
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) with totality (Ring.0R R) denomB
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl x) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inl _) = ringCanCancelPositive order 0<denomB p
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
    inter : ((numA * denomB) * denomC) < ((numB * denomA) * denomC)
    inter = ringCanMultiplyByPositive pRing 0<denomC a<b
    p : ((numA * denomC) * denomB) < ((numC * denomA) * denomB)
    p = SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) reflexive inter) (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByPositive pRing 0<denomA b<c))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inl _) = ringCanCancelNegative order denomB<0 (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) reflexive (ringCanMultiplyByPositive pRing 0<denomA b<c)) (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (ringCanMultiplyByPositive pRing 0<denomC a<b)))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) with totality (Ring.0R R) denomB
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inl 0<denomC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inr _) = ringCanCancelPositive order 0<denomB (SetoidPartialOrder.<Transitive pOrder have (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative pRing denomC<0 a<b)))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
    have : ((numC * denomA) * denomB) < ((numB * denomC)  * denomA)
    have = SetoidPartialOrder.<WellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByPositive pRing 0<denomA b<c)
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inr denomB<0) with totality (Ring.0R R) denomC
... | (inl (inl 0<denomC)) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
... | (inl (inr _)) = ringCanCancelNegative order denomB<0 (SetoidPartialOrder.<Transitive pOrder have (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByPositive pRing 0<denomA b<c)))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
    have : ((numA * denomC) * denomB) < ((numB * denomA) * denomC)
    have = SetoidPartialOrder.<WellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByNegative pRing denomC<0 a<b)
... | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) with totality (Ring.0R R) denomB
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inl _) = ringCanCancelPositive order 0<denomB (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative pRing denomA<0 b<c)) have)
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
    have : ((numB * denomA) * denomC) < ((numA * denomC) * denomB)
    have = SetoidPartialOrder.<WellDefined pOrder reflexive (swapLemma R) (ringCanMultiplyByPositive pRing 0<denomC a<b)
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inl _) = ringCanCancelNegative order denomB<0 (SetoidPartialOrder.<Transitive pOrder have (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative pRing denomA<0 b<c)))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
    have : ((numA * denomC) * denomB) < ((numB * denomA) * denomC)
    have = SetoidPartialOrder.<WellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByPositive pRing 0<denomC a<b)
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) with totality (Ring.0R R) denomB
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inl 0<denomC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inr _) = ringCanCancelPositive order 0<denomB (SetoidPartialOrder.<Transitive pOrder have (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative pRing denomA<0 b<c)))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
    have : ((numA * denomC) * denomB) < ((numB * denomA) * denomC)
    have = SetoidPartialOrder.<WellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByNegative pRing denomC<0 a<b)
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) with totality (Ring.0R R) denomC
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) | inl (inl 0<denomC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomC denomC<0))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) | inl (inr _) = ringCanCancelNegative order denomB<0 (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative pRing denomA<0 b<c)) have)
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
    have : ((numB * denomA) * denomC) < ((numA * denomC) * denomB)
    have = SetoidPartialOrder.<WellDefined pOrder reflexive (swapLemma R) (ringCanMultiplyByNegative pRing denomC<0 a<b)
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidPartialOrder.<Transitive (fieldOfFractionsOrder) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))

fieldOfFractionsTotalOrder : SetoidTotalOrder fieldOfFractionsOrder
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) with totality (Ring.0R R) denomA
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) with totality (Ring.0R R) denomB
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) with totality (Ring.0R R) denomA
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) with totality (numA * denomB) (numB * denomA)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) | inl (inl x) = inl (inl x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) | inl (inr x) = inl (inr x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) | inr x = inr (Equivalence.transitive (Setoid.eq S) x (Ring.*Commutative R))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inr denomA<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomA denomA<0))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) with totality (Ring.0R R) denomA
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) with totality (numB * denomA) (numA * denomB)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) | inl (inl x) = inl (inl x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) | inl (inr x) = inl (inr x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) | inr x = inr (Equivalence.symmetric (Setoid.eq S) (Equivalence.transitive (Setoid.eq S) (Ring.*Commutative R) x))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inr denomA<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomA denomA<0))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) with totality (Ring.0R R) denomB
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) with totality (Ring.0R R) denomA
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inl 0<denomA) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomA denomA<0))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) with totality (numB * denomA) (numA * denomB)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) | inl (inl x) = inl (inl x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) | inl (inr x) = inl (inr x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) | inr x = inr (Equivalence.transitive (Setoid.eq S) (Equivalence.symmetric (Setoid.eq S) x) (Ring.*Commutative R))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) with totality (Ring.0R R) denomA
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inl 0<denomA) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<denomA denomA<0))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) with totality (numA * denomB) (numB * denomA)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) | inl (inl x) = inl (inl x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) | inl (inr x) = inl (inr x)
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) | inr x = inr (Equivalence.transitive (Setoid.eq S) x (Ring.*Commutative R))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
SetoidTotalOrder.totality (fieldOfFractionsTotalOrder) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))

ineqLemma : {x y : A} → (Ring.0R R) < (x * y) → (Ring.0R R) < x → (Ring.0R R) < y
ineqLemma {x} {y} 0<xy 0<x with totality (Ring.0R R) y
ineqLemma {x} {y} 0<xy 0<x | inl (inl 0<y) = 0<y
ineqLemma {x} {y} 0<xy 0<x | inl (inr y<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<xy (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing y<0 0<x))))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
ineqLemma {x} {y} 0<xy 0<x | inr 0=y = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive (*WellDefined reflexive (symmetric 0=y)) (Ring.timesZero R)) 0<xy))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)

ineqLemma' : {x y : A} → (Ring.0R R) < (x * y) → x < (Ring.0R R) → y < (Ring.0R R)
ineqLemma' {x} {y} 0<xy x<0 with totality (Ring.0R R) y
... | inl (inl 0<y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<xy (SetoidPartialOrder.<WellDefined pOrder *Commutative (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing x<0 0<y))))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
... | inl (inr y<0) = y<0
... | (inr 0=y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive (*WellDefined reflexive (symmetric 0=y)) (Ring.timesZero R)) 0<xy))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)

ineqLemma'' : {x y : A} → (x * y) < (Ring.0R R) → (Ring.0R R) < x → y < (Ring.0R R)
ineqLemma'' {x} {y} xy<0 0<x with totality (Ring.0R R) y
... | inl (inl 0<y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder xy<0 (orderRespectsMultiplication 0<x 0<y)))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
... | inl (inr y<0) = y<0
... | (inr 0=y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (transitive (*WellDefined reflexive (symmetric 0=y)) (Ring.timesZero R)) reflexive xy<0))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)

ineqLemma''' : {x y : A} → (x * y) < (Ring.0R R) → x < (Ring.0R R) → (Ring.0R R) < y
ineqLemma''' {x} {y} xy<0 x<0 with totality (Ring.0R R) y
... | inl (inl 0<y) = 0<y
... | inl (inr y<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder xy<0 (SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) reflexive (ringCanMultiplyByNegative pRing y<0 x<0))))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)
... | inr 0=y = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (transitive (*WellDefined reflexive (symmetric 0=y)) (Ring.timesZero R)) reflexive xy<0))
  where
    open Setoid S
    open Ring R
    open Equivalence (Setoid.eq S)

fieldOfFractionsPOrderedRing : PartiallyOrderedRing fieldOfFractionsRing (SetoidTotalOrder.partial fieldOfFractionsTotalOrder)
PartiallyOrderedRing.orderRespectsAddition fieldOfFractionsPOrderedRing {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) with totality (Ring.0R R) (denomA * denomC)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) with totality (Ring.0R R) (denomB * denomC)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inl 0<dB) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByPositive pRing 0<dC (SetoidPartialOrder.<WellDefined pOrder (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (symmetric *DistributesOver+) *Commutative)) (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (symmetric *DistributesOver+) *Commutative)) ans))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC with totality 0R denomC
    0<dC | inl (inl x) = x
    0<dC | inl (inr dC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dBdC (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing dC<0 0<dB))))
    0<dC | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
    p : ((numA * denomC) * denomB) < ((numB * denomC) * denomA)
    p = SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByPositive pRing 0<dC a<b)
    ans : ((((numA * denomC) * denomB) + ((denomA * numC) * denomB))) < ((((numB * denomC) * denomA) + ((denomB * numC) * denomA)))
    ans = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (transitive (*WellDefined *Commutative reflexive) (transitive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (*WellDefined *Commutative reflexive)))) (PartiallyOrderedRing.orderRespectsAddition pRing p ((denomA * numC) * denomB))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inr dB<0) = exFalso bad
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 with totality 0R denomC
    ... | inl (inl x) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dBdC (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByPositive pRing x dB<0))))
    ... | inl (inr x) = x
    ... | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
    bad : False
    bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dAdC (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing dC<0 0<dA)))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inl 0<dB) = exFalso bad
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC with totality 0R denomC
    0<dC | inl (inl x) = x
    0<dC | inl (inr dC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dBdC (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing dC<0 0<dB))))
    0<dC | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
    dC<0 : denomC < 0R
    dC<0 with totality 0R denomC
    dC<0 | inl (inl 0<dC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dAdC (SetoidPartialOrder.<WellDefined pOrder *Commutative (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing dA<0 0<dC))))
    dC<0 | inl (inr x) = x
    dC<0 | inr x = exFalso (denomC!=0 (Equivalence.symmetric (Setoid.eq S) x))
    bad : False
    bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dC dC<0)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inr dB<0) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByNegative pRing dC<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric *DistributesOver+) *Commutative) (transitive (symmetric *DistributesOver+) *Commutative) have''))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 = ineqLemma' 0<dAdC dA<0
    have : ((numB * denomA) * denomC) < ((numA * denomB) * denomC)
    have = ringCanMultiplyByNegative pRing dC<0 a<b
    have' : (denomA * (numB * denomC)) < (denomB * (numA * denomC))
    have' = SetoidPartialOrder.<WellDefined pOrder (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)) (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)) have
    have'' : ((denomA * (numB * denomC)) + (denomA * (denomB * numC))) < ((denomB * (numA * denomC)) + (denomB * (denomA * numC)))
    have'' = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (transitive *Associative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)))) (PartiallyOrderedRing.orderRespectsAddition pRing have' (denomA * (denomB * numC)))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inl 0<dB) = exFalso bad
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC = ineqLemma 0<dAdC 0<dA
    dC<0 : denomC < 0R
    dC<0 = ineqLemma'' dBdC<0 0<dB
    bad : False
    bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dC dC<0)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inr dB<0) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByPositive pRing 0<dC ans)
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC = ineqLemma 0<dAdC 0<dA
    have : ((numB * denomA) * denomC) < ((numA * denomB) * denomC)
    have = ringCanMultiplyByPositive pRing 0<dC a<b
    have' : (((numB * denomC) * denomA) + ((denomB * numC) * denomA)) < (((numA * denomC) * denomB) + ((denomB * numC) * denomA))
    have' = PartiallyOrderedRing.orderRespectsAddition pRing (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) have) _
    ans : (((numB * denomC) + (denomB * numC)) * denomA) < (((numA * denomC) + (denomA * numC)) * denomB)
    ans = SetoidPartialOrder.<WellDefined pOrder (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (symmetric *DistributesOver+) *Commutative)) (transitive (Group.+WellDefined additiveGroup *Commutative (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative))) (transitive (symmetric *DistributesOver+) *Commutative)) have'
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inl 0<dB) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByNegative pRing dC<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (transitive (Group.+WellDefined additiveGroup reflexive (transitive *Associative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)))) (symmetric *DistributesOver+)) *Commutative)) (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (symmetric *DistributesOver+) *Commutative)) have))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 = ineqLemma'' dBdC<0 0<dB
    have : (((numA * denomC) * denomB) + ((denomB * numC) * denomA)) < (((numB * denomC) * denomA) + ((denomB * numC) * denomA))
    have = PartiallyOrderedRing.orderRespectsAddition pRing (SetoidPartialOrder.<WellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative pRing dC<0 a<b)) _
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inr dB<0) = exFalso bad
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 = ineqLemma' 0<dAdC dA<0
    0<dC : 0R < denomC
    0<dC = ineqLemma''' dBdC<0 dB<0
    bad : False
    bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dC dC<0)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inr 0=dBdC with IntegralDomain.intDom I (Equivalence.symmetric (Setoid.eq S) 0=dBdC)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inr 0=dBdC | f = exFalso (denomC!=0 (f denomB!=0))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) with totality (Ring.0R R) (denomB * denomC)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inl 0<dB) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dC dC<0))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC = ineqLemma 0<dBdC 0<dB
    dC<0 : denomC < 0R
    dC<0 = ineqLemma'' dAdC<0 0<dA
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inr dB<0) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByNegative pRing dC<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (Group.+WellDefined additiveGroup (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)) *Commutative) (transitive (symmetric *DistributesOver+) *Commutative)) (transitive (Group.+WellDefined additiveGroup (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)) (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative))) (transitive (symmetric *DistributesOver+) *Commutative)) have))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 = ineqLemma'' dAdC<0 0<dA
    have : (((numA * denomB) * denomC) + ((denomA * numC) * denomB)) < (((numB * denomA) * denomC) + ((denomA * numC) * denomB))
    have = PartiallyOrderedRing.orderRespectsAddition pRing (ringCanMultiplyByNegative pRing dC<0 a<b) _
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) | inr 0=dB = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) 0=dB))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inl 0<dB) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByPositive pRing 0<dC (SetoidPartialOrder.<WellDefined pOrder (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (transitive (Group.+WellDefined additiveGroup (transitive *Commutative (transitive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) *Commutative)) (transitive *Associative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)))) (symmetric *DistributesOver+)) *Commutative)) (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (transitive (Group.+WellDefined additiveGroup (transitive *Commutative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative))) reflexive) (symmetric *DistributesOver+)) *Commutative)) have))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC = ineqLemma 0<dBdC 0<dB
    have : (((numB * denomA) * denomC) + ((denomA * numC) * denomB)) < (((numA * denomB) * denomC) + ((denomA * numC) * denomB))
    have = PartiallyOrderedRing.orderRespectsAddition pRing (ringCanMultiplyByPositive pRing 0<dC a<b) _
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inr dB<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dC dC<0))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 = ineqLemma' 0<dBdC dB<0
    0<dC : 0R < denomC
    0<dC = ineqLemma''' dAdC<0 dA<0
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) | inr 0=dB = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) 0=dB))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inr 0=dA = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) 0=dA))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inl 0<dB) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByNegative pRing dC<0 (SetoidPartialOrder.<WellDefined pOrder (transitive (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (Group.+WellDefined additiveGroup (transitive *Commutative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative))) reflexive)) (transitive (symmetric *DistributesOver+) *Commutative)) (transitive (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (Group.+WellDefined additiveGroup (transitive (transitive *Associative (*WellDefined *Commutative reflexive)) *Commutative) (transitive *Associative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative))))) (transitive (symmetric *DistributesOver+) *Commutative)) have))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 = ineqLemma'' dAdC<0 0<dA
    have : (((numB * denomA) * denomC) + ((denomB * numC) * denomA)) < (((numA * denomB) * denomC) + ((denomB * numC) * denomA))
    have = PartiallyOrderedRing.orderRespectsAddition pRing (ringCanMultiplyByNegative pRing dC<0 a<b) _
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inr dB<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder dC<0 0<dC))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    dC<0 : denomC < 0R
    dC<0 = ineqLemma'' dAdC<0 0<dA
    0<dC : 0R < denomC
    0<dC = ineqLemma''' dBdC<0 dB<0
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inl 0<dB) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dC dC<0))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC = ineqLemma''' dAdC<0 dA<0
    dC<0 : denomC < 0R
    dC<0 = ineqLemma'' dBdC<0 0<dB
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inr dB<0) = SetoidPartialOrder.<WellDefined pOrder (symmetric *Associative) (symmetric *Associative) (ringCanMultiplyByPositive pRing 0<dC (SetoidPartialOrder.<WellDefined pOrder (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (Group.+WellDefined additiveGroup (transitive *Commutative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative))) reflexive) (transitive (symmetric *DistributesOver+) *Commutative))) (transitive (Group.+WellDefined additiveGroup *Commutative *Commutative) (transitive (transitive (Group.+WellDefined additiveGroup (transitive *Commutative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative))) (transitive *Commutative (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative)))) (symmetric *DistributesOver+)) *Commutative)) have))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<dC : 0R < denomC
    0<dC = ineqLemma''' dAdC<0 dA<0
    have : (((numA * denomB) * denomC) + ((denomA * numC) * denomB)) < (((numB * denomA) * denomC) + ((denomA * numC) * denomB))
    have = PartiallyOrderedRing.orderRespectsAddition pRing (ringCanMultiplyByPositive pRing 0<dC a<b) _
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inr 0=dBdC with IntegralDomain.intDom I (Equivalence.symmetric (Setoid.eq S) 0=dBdC)
... | f = exFalso (denomC!=0 (f denomB!=0))
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inr (0=dAdC) with IntegralDomain.intDom I (Equivalence.symmetric (Setoid.eq S) 0=dAdC)
PartiallyOrderedRing.orderRespectsAddition (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inr 0=dAdC | f = exFalso (denomC!=0 (f denomA!=0))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} t u with totality (Ring.0R R) (Ring.1R R)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) with totality (Ring.0R R) (denomA * denomB)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) | inl (inl 0<dA) = SetoidPartialOrder.<WellDefined pOrder (symmetric (transitive *Commutative (Ring.timesZero R))) (symmetric (transitive *Commutative identIsIdent)) 0<nAnB
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<nA : 0R < numA
    0<nA = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) (transitive *Commutative identIsIdent) 0<a
    0<nB : 0R < numB
    0<nB = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) (transitive *Commutative identIsIdent) 0<b
    0<nAnB : 0R < (numA * numB)
    0<nAnB = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) reflexive (ringCanMultiplyByPositive pRing 0<nB 0<nA)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) | inl (inr dA<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dAdB (SetoidPartialOrder.<WellDefined pOrder *Commutative (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing dA<0 0<dB))))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) | inl (inl 0<dA) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 0<dAdB (SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing dB<0 0<dA))))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) | inl (inr dA<0) = SetoidPartialOrder.<WellDefined pOrder (symmetric (transitive *Commutative (Ring.timesZero R))) (symmetric (transitive *Commutative identIsIdent)) 0<nAnB
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    nB<0 : numB < 0R
    nB<0 = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative identIsIdent) (transitive *Commutative (Ring.timesZero R)) 0<b
    nA<0 : numA < 0R
    nA<0 = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative identIsIdent) (transitive *Commutative (Ring.timesZero R)) 0<a
    0<nAnB : 0R < (numA * numB)
    0<nAnB = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) *Commutative (ringCanMultiplyByNegative pRing nA<0 nB<0)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) with totality (Ring.0R R) denomB
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) | inl (inl 0<denomA) = exFalso f
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    f : False
    f with PartiallyOrderedRing.orderRespectsMultiplication pRing 0<denomA 0<denomB
    ... | bl = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder bl dAdB<0)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) | inl (inr denomA<0) = SetoidPartialOrder.<WellDefined pOrder (symmetric (transitive *Commutative identIsIdent)) (symmetric (transitive *Commutative (Ring.timesZero R))) ans
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    0<nB : 0R < numB
    0<nB = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) (transitive *Commutative identIsIdent) 0<b
    nA<0 : numA < 0R
    nA<0 = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative identIsIdent) (transitive *Commutative (Ring.timesZero R)) 0<a
    ans : (numA * numB) < 0R
    ans = SetoidPartialOrder.<WellDefined pOrder *Commutative (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing nA<0 0<nB)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) with totality (Ring.0R R) denomA
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) | inl (inl 0<denomA) = SetoidPartialOrder.<WellDefined pOrder (symmetric (transitive *Commutative identIsIdent)) (symmetric (transitive *Commutative (Ring.timesZero R))) nAnB<0
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    nB<0 : numB < 0R
    nB<0 = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative identIsIdent) (transitive *Commutative (Ring.timesZero R)) 0<b
    0<nA : 0R < numA
    0<nA = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) (transitive *Commutative identIsIdent) 0<a
    nAnB<0 : (numA * numB) < 0R
    nAnB<0 = SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (Ring.timesZero R)) (ringCanMultiplyByNegative pRing nB<0 0<nA)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) | inl (inr denomA<0) = exFalso f
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
    h : 0R < (denomA * denomB)
    h = SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) reflexive (ringCanMultiplyByNegative pRing denomB<0 denomA<0)
    f : False
    f = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder dAdB<0 h)
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) | inr x = exFalso (denomA!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inr x = exFalso (denomB!=0 (Equivalence.symmetric (Setoid.eq S) x))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inr 0=dAdB with IntegralDomain.intDom I (Equivalence.symmetric (Setoid.eq S) 0=dAdB)
... | f = exFalso (denomB!=0 (f denomA!=0))
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inr 1<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder 1<0 (SetoidPartialOrder.<WellDefined pOrder (transitive *Commutative (Ring.timesZero R)) identIsIdent (ringCanMultiplyByNegative pRing 1<0 1<0))))
  where
    open Setoid S
    open Equivalence (Setoid.eq S)
    open Ring R
PartiallyOrderedRing.orderRespectsMultiplication (fieldOfFractionsPOrderedRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inr x = exFalso (IntegralDomain.nontrivial I (Equivalence.symmetric (Setoid.eq S) x))

fieldOfFractionsOrderedRing : TotallyOrderedRing fieldOfFractionsPOrderedRing
TotallyOrderedRing.total fieldOfFractionsOrderedRing = fieldOfFractionsTotalOrder
