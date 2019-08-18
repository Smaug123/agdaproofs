{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Rings.Lemmas
open import Rings.IntegralDomains
open import Fields.Fields
open import Functions
open import Setoids.Setoids
open import Setoids.Orders
open import Fields.FieldOfFractions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.FieldOfFractionsOrder where

  fieldOfFractionsComparison : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → Rel (fieldOfFractionsSet I)
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) = (numA * denomB) < (numB * denomA)
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) = (numB * denomA) < (numA * denomB)
  fieldOfFractionsComparison {S = S} {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inr 0=denomB = exFalso (denomB!=0 (symmetric 0=denomB))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) = (numB * denomA) < (numA * denomB)
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) = (numA * denomB) < (numB * denomA)
  fieldOfFractionsComparison {S = S} {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inr 0=denomB = exFalso (denomB!=0 (symmetric 0=denomB))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  fieldOfFractionsComparison {S = S} {_*_ = _*_} {R} {_<_} {tOrder = tOrder} i oring (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inr 0=denomA = exFalso (denomA!=0 (symmetric 0=denomA))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  fieldOfFractionsOrderWellDefinedLeft : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → {x y z : fieldOfFractionsSet I} → fieldOfFractionsComparison I order x y → Setoid._∼_ (fieldOfFractionsSetoid I) x z → fieldOfFractionsComparison I order z y
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R = R} {tOrder = tOrder} I order {(numX ,, (denomX , denomX!=0))} {(numY ,, (denomY , denomY!=0))} {(numZ ,, (denomZ , denomZ!=0))} x<y x=z with SetoidTotalOrder.totality tOrder (Ring.0R R) denomZ
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomX
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inl _) = s
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      have : ((numX * denomY) * denomZ) < ((numY * denomX) * denomZ)
      have = ringCanMultiplyByPositive order 0<denomZ x<y
      p : ((numX * denomZ) * denomY) < ((numY * denomX) * denomZ)
      p = SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) reflexive have
      q : ((denomX * numZ) * denomY) < ((numY * denomX) * denomZ)
      q = SetoidPartialOrder.wellDefined pOrder (multWellDefined x=z reflexive) reflexive p
      r : ((numZ * denomY) * denomX) < ((numY * denomZ) * denomX)
      r = SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) multCommutative) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) q
      s : (numZ * denomY) < (numY * denomZ)
      s = ringCanCancelPositive order 0<denomX r
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inr x) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomY x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (symmetric x))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inl _) = ringCanCancelNegative order denomX<0 r
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      p : ((numY * denomX) * denomZ) < ((numX * denomZ) * denomY)
      p = SetoidPartialOrder.wellDefined pOrder reflexive (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByPositive order 0<denomZ x<y)
      q : ((numY * denomX) * denomZ) < ((denomX * numZ) * denomY)
      q = SetoidPartialOrder.wellDefined pOrder reflexive (multWellDefined x=z reflexive) p
      r : ((numY * denomZ) * denomX) < ((numZ * denomY) * denomX)
      r = SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) multCommutative) q
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inr x) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomY x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inl (inr denomX<0) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inl 0<denomY) | inr 0=denomX = exFalso (denomX!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=denomX))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomX
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomY denomY<0))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inr _) = ringCanCancelPositive order 0<denomX r
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      p : ((numY * denomX) * denomZ) < ((numX * denomY) * denomZ)
      p = ringCanMultiplyByPositive order 0<denomZ x<y
      q : ((numY * denomX) * denomZ) < ((denomX * numZ) * denomY)
      q = SetoidPartialOrder.wellDefined pOrder reflexive (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (multWellDefined x=z reflexive)))) p
      r : ((numY * denomZ) * denomX) < ((numZ * denomY) * denomX)
      r = SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) multCommutative) q
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomY denomY<0))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inr _) = ringCanCancelNegative order denomX<0 q
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      p : ((numX * denomY) * denomZ) < ((numY * denomX) * denomZ)
      p = ringCanMultiplyByPositive order 0<denomZ x<y
      q : ((numZ * denomY) * denomX) < ((numY * denomZ) * denomX)
      q = SetoidPartialOrder.wellDefined pOrder (transitive (multWellDefined multCommutative reflexive) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive x=z) (transitive multCommutative (transitive (symmetric multAssoc) multCommutative))))) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) p
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inl (inr denomX<0) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inl (inr denomY<0) | inr 0=denomX = exFalso (denomX!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=denomX))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inl 0<denomZ) | inr 0=denomY = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=denomY))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomX
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inl _) = ringCanCancelPositive order 0<denomX (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive x=z) (transitive (multWellDefined reflexive (multCommutative)) (transitive multAssoc (multWellDefined multCommutative reflexive))))) p)
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      p : ((numY * denomX) * denomZ) < ((denomY * numX) * denomZ)
      p = ringCanMultiplyByNegative order denomZ<0 (SetoidPartialOrder.wellDefined pOrder multCommutative reflexive x<y)
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) | inl (inr denomY<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomY denomY<0))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inl _) = ringCanCancelNegative order denomX<0 (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined x=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) p)
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      p : ((numX * denomY) * denomZ) < ((numY * denomX) * denomZ)
      p = ringCanMultiplyByNegative order denomZ<0 x<y
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) | inl (inr denomY<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder denomY<0 0<denomY))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inl (inr denomX<0) | inr 0=denomY = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=denomY))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inl 0<denomY) | inr x = exFalso (denomX!=0 (symmetric x))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomX
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomY denomY<0))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) | inl (inr _) = ringCanCancelPositive order 0<denomX (SetoidPartialOrder.wellDefined pOrder (transitive (multWellDefined multCommutative reflexive) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive x=z) (transitive multAssoc (transitive multCommutative multAssoc))))) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByNegative order denomZ<0 x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inl 0<denomX) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inl 0<denomY) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomY denomY<0))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) | inl (inr _) = ringCanCancelNegative order denomX<0 (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (multWellDefined multCommutative reflexive) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive x=z) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (multWellDefined multCommutative reflexive)))))) (ringCanMultiplyByNegative order denomZ<0 x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inl (inr denomX<0) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inl (inr denomY<0) | inr x = exFalso (denomX!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inl (inr denomZ<0) | inr x = exFalso (denomY!=0 (symmetric x))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedLeft {S = S} {_*_ = _*_} {R} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y x=z | inr 0=denomZ = exFalso (denomZ!=0 (symmetric 0=denomZ))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  fieldOfFractionsOrderWellDefinedRight : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → {x y z : fieldOfFractionsSet I} → fieldOfFractionsComparison I order x y → Setoid._∼_ (fieldOfFractionsSetoid I) y z → fieldOfFractionsComparison I order x z
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R = R} {pOrder = pOrder} {tOrder = tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z with SetoidTotalOrder.totality tOrder (Ring.0R R) denomX
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomZ
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (ringCanMultiplyByPositive order 0<denomZ x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByPositive order 0<denomZ x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inl 0<denomZ) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByNegative order denomZ<0 x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive (multAssoc) (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (ringCanMultiplyByNegative order denomZ<0 x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inl (inr denomZ<0) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inl 0<denomX) | inr x = exFalso (denomZ!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomZ
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByPositive order 0<denomZ x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (ringCanMultiplyByPositive order 0<denomZ x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inl 0<denomZ) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomY
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) | inl (inl 0<denomY) = ringCanCancelPositive order 0<denomY (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (ringCanMultiplyByNegative order denomZ<0 x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) | inl (inr denomY<0) = ringCanCancelNegative order denomY<0 (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined y=z reflexive) (transitive (symmetric multAssoc) multCommutative))))) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByNegative order denomZ<0 x<y))
    where
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inl (inr denomZ<0) | inr x = exFalso (denomY!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inl (inr denomX<0) | inr x = exFalso (denomZ!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  fieldOfFractionsOrderWellDefinedRight {S = S} {_*_ = _*_} {R} {pOrder = pOrder} {tOrder} I order {numX ,, (denomX , denomX!=0)} {numY ,, (denomY , denomY!=0)} {numZ ,, (denomZ , denomZ!=0)} x<y y=z | inr x = exFalso (denomX!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))

  swapLemma : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) {x y z : A} → Setoid._∼_ S ((x * y) * z) ((x * z) * y)
  swapLemma {S = S} R = transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))

  fieldOfFractionsOrder : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → SetoidPartialOrder (fieldOfFractionsSetoid I) (fieldOfFractionsComparison I order)
  SetoidPartialOrder.wellDefined (fieldOfFractionsOrder I oRing) {a} {b} {c} {d} a=b c=d a<c = fieldOfFractionsOrderWellDefinedRight I oRing {b} {c} {d} (fieldOfFractionsOrderWellDefinedLeft I oRing {a} {c} {b} a<c a=b) c=d
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder = tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr with SetoidTotalOrder.totality tOrder (Ring.0R R) aDenom
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) with SetoidTotalOrder.totality tOrder (Ring.0R R) aDenom
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) | inl (inl _) = SetoidPartialOrder.irreflexive pOrder pr
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) | inl (inr aDenom<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<aDenom aDenom<0))
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inl 0<aDenom) | inr x = exFalso (aDenom!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) aDenom
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) | inl (inl 0<aDenom) = SetoidPartialOrder.irreflexive pOrder pr
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) | inl (inr _) = SetoidPartialOrder.irreflexive pOrder pr
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inl (inr aDenom<0) | inr x = exFalso (aDenom!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {aNum ,, (aDenom , aDenom!=0)} pr | inr x = exFalso (aDenom!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder = tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl x) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inl _) = ringCanCancelPositive oRing 0<denomB p
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      inter : ((numA * denomB) * denomC) < ((numB * denomA) * denomC)
      inter = ringCanMultiplyByPositive oRing 0<denomC a<b
      p : ((numA * denomC) * denomB) < ((numC * denomA) * denomB)
      p = SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) reflexive inter) (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByPositive oRing 0<denomA b<c))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inl _) = ringCanCancelNegative oRing denomB<0 (SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) reflexive (ringCanMultiplyByPositive oRing 0<denomA b<c)) (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (ringCanMultiplyByPositive oRing 0<denomC a<b)))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inl (inr denomB<0) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inl 0<denomC) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inl 0<denomC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inr _) = ringCanCancelPositive oRing 0<denomB (SetoidPartialOrder.transitive pOrder have (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative oRing denomC<0 a<b)))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      have : ((numC * denomA) * denomB) < ((numB * denomC)  * denomA)
      have = SetoidPartialOrder.wellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByPositive oRing 0<denomA b<c)
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inl (inr denomB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  ... | (inl (inl 0<denomC)) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  ... | (inl (inr _)) = ringCanCancelNegative oRing denomB<0 (SetoidPartialOrder.transitive pOrder have (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByPositive oRing 0<denomA b<c)))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      have : ((numA * denomC) * denomB) < ((numB * denomA) * denomC)
      have = SetoidPartialOrder.wellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByNegative oRing denomC<0 a<b)
  ... | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inl (inr denomC<0) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inl 0<denomA) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inl _) = ringCanCancelPositive oRing 0<denomB (SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative oRing denomA<0 b<c)) have)
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      have : ((numB * denomA) * denomC) < ((numA * denomC) * denomB)
      have = SetoidPartialOrder.wellDefined pOrder reflexive (swapLemma R) (ringCanMultiplyByPositive oRing 0<denomC a<b)
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inl _) = ringCanCancelNegative oRing denomB<0 (SetoidPartialOrder.transitive pOrder have (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative oRing denomA<0 b<c)))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      have : ((numA * denomC) * denomB) < ((numB * denomA) * denomC)
      have = SetoidPartialOrder.wellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByPositive oRing 0<denomC a<b)
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) | inl (inr denomC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inl (inr denomB<0) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {a} {b} {c} {A} {S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inl 0<denomC) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inl 0<denomC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) | inl (inr _) = ringCanCancelPositive oRing 0<denomB (SetoidPartialOrder.transitive pOrder have (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative oRing denomA<0 b<c)))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      have : ((numA * denomC) * denomB) < ((numB * denomA) * denomC)
      have = SetoidPartialOrder.wellDefined pOrder (swapLemma R) reflexive (ringCanMultiplyByNegative oRing denomC<0 a<b)
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inl 0<denomB) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomC
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) | inl (inl 0<denomC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomC denomC<0))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) | inl (inr _) = ringCanCancelNegative oRing denomB<0 (SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative oRing denomA<0 b<c)) have)
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      have : ((numB * denomA) * denomC) < ((numA * denomC) * denomB)
      have = SetoidPartialOrder.wellDefined pOrder reflexive (swapLemma R) (ringCanMultiplyByNegative oRing denomC<0 a<b)
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inl (inr denomB<0) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inl (inr denomC<0) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inl (inr denomA<0) | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} {numC ,, (denomC , denomC!=0)} a<b b<c | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))

  fieldOfFractionsTotalOrder : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → SetoidTotalOrder (fieldOfFractionsOrder I order)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) with SetoidTotalOrder.totality tOrder (numA * denomB) (numB * denomA)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) | inl (inl x) = inl (inl x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) | inl (inr x) = inl (inr x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inl _) | inr x = inr (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) x (Ring.multCommutative R))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inl (inr denomA<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomA denomA<0))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inl 0<denomB) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) with SetoidTotalOrder.totality tOrder (numB * denomA) (numA * denomB)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) | inl (inl x) = inl (inl x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) | inl (inr x) = inl (inr x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inl _) | inr x = inr (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) (Ring.multCommutative R) x))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inl (inr denomA<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomA denomA<0))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inl (inr denomB<0) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inl 0<denomA) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inl 0<denomA) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomA denomA<0))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) with SetoidTotalOrder.totality tOrder (numB * denomA) (numA * denomB)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) | inl (inl x) = inl (inl x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) | inl (inr x) = inl (inr x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inl (inr _) | inr x = inr (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x) (Ring.multCommutative R))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inl 0<denomB) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inl 0<denomA) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<denomA denomA<0))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) with SetoidTotalOrder.totality tOrder (numA * denomB) (numB * denomA)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) | inl (inl x) = inl (inl x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) | inl (inr x) = inl (inr x)
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inl (inr _) | inr x = inr (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) x (Ring.multCommutative R))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inl (inr denomB<0) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inl (inr denomA<0) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  SetoidTotalOrder.totality (fieldOfFractionsTotalOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) (numA ,, (denomA , denomA!=0)) (numB ,, (denomB , denomB!=0)) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))

  ineqLemma : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → {x y : A} → (Ring.0R R) < (x * y) → (Ring.0R R) < x → (Ring.0R R) < y
  ineqLemma {S = S} {R = R} {_<_ = _<_} {tOrder = tOrder} I order {x} {y} 0<xy 0<x with SetoidTotalOrder.totality tOrder (Ring.0R R) y
  ineqLemma {S = S} {R = R} {_<_} {tOrder = tOrder} I order {x} {y} 0<xy 0<x | inl (inl 0<y) = 0<y
  ineqLemma {S = S} {R = R} {_<_} {pOrder = pOrder} {tOrder = tOrder} I order {x} {y} 0<xy 0<x | inl (inr y<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<xy (SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative order y<0 0<x))))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  ineqLemma {S = S} {R = R} {_<_} {pOrder = pOrder} {tOrder = tOrder} I order {x} {y} 0<xy 0<x | inr 0=y = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder reflexive (transitive (multWellDefined reflexive (symmetric 0=y)) (ringTimesZero R)) 0<xy))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))

  ineqLemma' : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → {x y : A} → (Ring.0R R) < (x * y) → x < (Ring.0R R) → y < (Ring.0R R)
  ineqLemma' {S = S} {R = R} {_<_} {pOrder = pOrder} {tOrder = tOrder} I order {x} {y} 0<xy x<0 with SetoidTotalOrder.totality tOrder (Ring.0R R) y
  ... | inl (inl 0<y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<xy (SetoidPartialOrder.wellDefined pOrder multCommutative (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative order x<0 0<y))))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  ... | inl (inr y<0) = y<0
  ... | (inr 0=y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder reflexive (transitive (multWellDefined reflexive (symmetric 0=y)) (ringTimesZero R)) 0<xy))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))

  ineqLemma'' : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → {x y : A} → (x * y) < (Ring.0R R) → (Ring.0R R) < x → y < (Ring.0R R)
  ineqLemma'' {S = S} {R = R} {_<_} {pOrder = pOrder} {tOrder = tOrder} I order {x} {y} xy<0 0<x with SetoidTotalOrder.totality tOrder (Ring.0R R) y
  ... | inl (inl 0<y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder xy<0 (OrderedRing.orderRespectsMultiplication order 0<x 0<y)))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  ... | inl (inr y<0) = y<0
  ... | (inr 0=y) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder (transitive (multWellDefined reflexive (symmetric 0=y)) (ringTimesZero R)) reflexive xy<0))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))

  ineqLemma''' : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → {x y : A} → (x * y) < (Ring.0R R) → x < (Ring.0R R) → (Ring.0R R) < y
  ineqLemma''' {S = S} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder} {tOrder} I order {x} {y} xy<0 x<0 with SetoidTotalOrder.totality tOrder (Ring.0R R) y
  ... | inl (inl 0<y) = 0<y
  ... | inl (inr y<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder xy<0 (SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) reflexive (ringCanMultiplyByNegative order y<0 x<0))))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  ... | inr 0=y = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder (transitive (multWellDefined reflexive (symmetric 0=y)) (ringTimesZero R)) reflexive xy<0))
    where
      open Setoid S
      open Ring R
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))

  fieldOfFractionsOrderedRing : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → OrderedRing (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I order)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) with SetoidTotalOrder.totality tOrder (Ring.0R R) (denomA * denomC)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) with SetoidTotalOrder.totality tOrder (Ring.0R R) (denomB * denomC)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inl 0<dB) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByPositive oRing 0<dC (SetoidPartialOrder.wellDefined pOrder (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (symmetric multDistributes) multCommutative)) (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (symmetric multDistributes) multCommutative)) ans))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC with SetoidTotalOrder.totality tOrder 0R denomC
      0<dC | inl (inl x) = x
      0<dC | inl (inr dC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dBdC (SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing dC<0 0<dB))))
      0<dC | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
      p : ((numA * denomC) * denomB) < ((numB * denomC) * denomA)
      p = SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByPositive oRing 0<dC a<b)
      ans : ((((numA * denomC) * denomB) + ((denomA * numC) * denomB))) < ((((numB * denomC) * denomA) + ((denomB * numC) * denomA)))
      ans = SetoidPartialOrder.wellDefined pOrder reflexive (Group.wellDefined additiveGroup reflexive (transitive (multWellDefined multCommutative reflexive) (transitive (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (multWellDefined multCommutative reflexive)))) (OrderedRing.orderRespectsAddition oRing p ((denomA * numC) * denomB))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inr dB<0) = exFalso bad
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 with SetoidTotalOrder.totality tOrder 0R denomC
      ... | inl (inl x) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dBdC (SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByPositive oRing x dB<0))))
      ... | inl (inr x) = x
      ... | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
      bad : False
      bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dAdC (SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing dC<0 0<dA)))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inl 0<dA) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inl 0<dB) = exFalso bad
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC with SetoidTotalOrder.totality tOrder 0R denomC
      0<dC | inl (inl x) = x
      0<dC | inl (inr dC<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dBdC (SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing dC<0 0<dB))))
      0<dC | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
      dC<0 : denomC < 0R
      dC<0 with SetoidTotalOrder.totality tOrder 0R denomC
      dC<0 | inl (inl 0<dC) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dAdC (SetoidPartialOrder.wellDefined pOrder multCommutative (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing dA<0 0<dC))))
      dC<0 | inl (inr x) = x
      dC<0 | inr x = exFalso (denomC!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
      bad : False
      bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dC dC<0)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inr dB<0) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByNegative oRing dC<0 (SetoidPartialOrder.wellDefined pOrder (transitive (symmetric multDistributes) multCommutative) (transitive (symmetric multDistributes) multCommutative) have''))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 = ineqLemma' I oRing 0<dAdC dA<0
      have : ((numB * denomA) * denomC) < ((numA * denomB) * denomC)
      have = ringCanMultiplyByNegative oRing dC<0 a<b
      have' : (denomA * (numB * denomC)) < (denomB * (numA * denomC))
      have' = SetoidPartialOrder.wellDefined pOrder (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc)) (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc)) have
      have'' : ((denomA * (numB * denomC)) + (denomA * (denomB * numC))) < ((denomB * (numA * denomC)) + (denomB * (denomA * numC)))
      have'' = SetoidPartialOrder.wellDefined pOrder reflexive (Group.wellDefined additiveGroup reflexive (transitive multAssoc (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc)))) (OrderedRing.orderRespectsAddition oRing have' (denomA * (denomB * numC)))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inl (inr dA<0) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inl 0<dBdC) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inl 0<dB) = exFalso bad
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC = ineqLemma I oRing 0<dAdC 0<dA
      dC<0 : denomC < 0R
      dC<0 = ineqLemma'' I oRing dBdC<0 0<dB
      bad : False
      bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dC dC<0)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inr dB<0) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByPositive oRing 0<dC ans)
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC = ineqLemma I oRing 0<dAdC 0<dA
      have : ((numB * denomA) * denomC) < ((numA * denomB) * denomC)
      have = ringCanMultiplyByPositive oRing 0<dC a<b
      have' : (((numB * denomC) * denomA) + ((denomB * numC) * denomA)) < (((numA * denomC) * denomB) + ((denomB * numC) * denomA))
      have' = OrderedRing.orderRespectsAddition oRing (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) have) _
      ans : (((numB * denomC) + (denomB * numC)) * denomA) < (((numA * denomC) + (denomA * numC)) * denomB)
      ans = SetoidPartialOrder.wellDefined pOrder (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (symmetric multDistributes) multCommutative)) (transitive (Group.wellDefined additiveGroup multCommutative (transitive (symmetric multAssoc) (multWellDefined reflexive multCommutative))) (transitive (symmetric multDistributes) multCommutative)) have'
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inl 0<dA) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inl 0<dB) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByNegative oRing dC<0 (SetoidPartialOrder.wellDefined pOrder (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (transitive (Group.wellDefined additiveGroup reflexive (transitive multAssoc (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc)))) (symmetric multDistributes)) multCommutative)) (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (symmetric multDistributes) multCommutative)) have))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 = ineqLemma'' I oRing dBdC<0 0<dB
      have : (((numA * denomC) * denomB) + ((denomB * numC) * denomA)) < (((numB * denomC) * denomA) + ((denomB * numC) * denomA))
      have = OrderedRing.orderRespectsAddition oRing (SetoidPartialOrder.wellDefined pOrder (swapLemma R) (swapLemma R) (ringCanMultiplyByNegative oRing dC<0 a<b)) _
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inr dB<0) = exFalso bad
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 = ineqLemma' I oRing 0<dAdC dA<0
      0<dC : 0R < denomC
      0<dC = ineqLemma''' I oRing dBdC<0 dB<0
      bad : False
      bad = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dC dC<0)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inl (inr dA<0) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inl (inr dBdC<0) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inr 0=dBdC with IntegralDomain.intDom I (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=dBdC)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inr 0=dBdC | inl x = exFalso (denomB!=0 x)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inl 0<dAdC) | inr 0=dBdC | inr x = exFalso (denomC!=0 x)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) (denomB * denomC)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inl 0<dB) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dC dC<0))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC = ineqLemma I oRing 0<dBdC 0<dB
      dC<0 : denomC < 0R
      dC<0 = ineqLemma'' I oRing dAdC<0 0<dA
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) | inl (inr dB<0) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByNegative oRing dC<0 (SetoidPartialOrder.wellDefined pOrder (transitive (Group.wellDefined additiveGroup (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc)) multCommutative) (transitive (symmetric multDistributes) multCommutative)) (transitive (Group.wellDefined additiveGroup (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc)) (transitive (symmetric multAssoc) (multWellDefined reflexive multCommutative))) (transitive (symmetric multDistributes) multCommutative)) have))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 = ineqLemma'' I oRing dAdC<0 0<dA
      have : (((numA * denomB) * denomC) + ((denomA * numC) * denomB)) < (((numB * denomA) * denomC) + ((denomA * numC) * denomB))
      have = OrderedRing.orderRespectsAddition oRing (ringCanMultiplyByNegative oRing dC<0 a<b) _
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inl 0<dA) | inr 0=dB = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=dB))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inl 0<dB) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByPositive oRing 0<dC (SetoidPartialOrder.wellDefined pOrder (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (transitive (Group.wellDefined additiveGroup (transitive multCommutative (transitive (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) multCommutative)) (transitive multAssoc (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc)))) (symmetric multDistributes)) multCommutative)) (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (transitive (Group.wellDefined additiveGroup (transitive multCommutative (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc))) reflexive) (symmetric multDistributes)) multCommutative)) have))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC = ineqLemma I oRing 0<dBdC 0<dB
      have : (((numB * denomA) * denomC) + ((denomA * numC) * denomB)) < (((numA * denomB) * denomC) + ((denomA * numC) * denomB))
      have = OrderedRing.orderRespectsAddition oRing (ringCanMultiplyByPositive oRing 0<dC a<b) _
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) | inl (inr dB<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dC dC<0))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 = ineqLemma' I oRing 0<dBdC dB<0
      0<dC : 0R < denomC
      0<dC = ineqLemma''' I oRing dAdC<0 dA<0
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inl (inr dA<0) | inr 0=dB = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=dB))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inl 0<dBdC) | inr 0=dA = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=dA))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inl 0<dB) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByNegative oRing dC<0 (SetoidPartialOrder.wellDefined pOrder (transitive (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (Group.wellDefined additiveGroup (transitive multCommutative (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc))) reflexive)) (transitive (symmetric multDistributes) multCommutative)) (transitive (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (Group.wellDefined additiveGroup (transitive (transitive multAssoc (multWellDefined multCommutative reflexive)) multCommutative) (transitive multAssoc (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc))))) (transitive (symmetric multDistributes) multCommutative)) have))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 = ineqLemma'' I oRing dAdC<0 0<dA
      have : (((numB * denomA) * denomC) + ((denomB * numC) * denomA)) < (((numA * denomB) * denomC) + ((denomB * numC) * denomA))
      have = OrderedRing.orderRespectsAddition oRing (ringCanMultiplyByNegative oRing dC<0 a<b) _
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) | inl (inr dB<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder dC<0 0<dC))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      dC<0 : denomC < 0R
      dC<0 = ineqLemma'' I oRing dAdC<0 0<dA
      0<dC : 0R < denomC
      0<dC = ineqLemma''' I oRing dBdC<0 dB<0
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inl 0<dA) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inl 0<dB) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dC dC<0))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC = ineqLemma''' I oRing dAdC<0 dA<0
      dC<0 : denomC < 0R
      dC<0 = ineqLemma'' I oRing dBdC<0 0<dB
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) | inl (inr dB<0) = SetoidPartialOrder.wellDefined pOrder (symmetric multAssoc) (symmetric multAssoc) (ringCanMultiplyByPositive oRing 0<dC (SetoidPartialOrder.wellDefined pOrder (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (Group.wellDefined additiveGroup (transitive multCommutative (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc))) reflexive) (transitive (symmetric multDistributes) multCommutative))) (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (transitive (Group.wellDefined additiveGroup (transitive multCommutative (transitive (multWellDefined multCommutative reflexive) (symmetric multAssoc))) (transitive multCommutative (transitive (symmetric multAssoc) (multWellDefined reflexive multCommutative)))) (symmetric multDistributes)) multCommutative)) have))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<dC : 0R < denomC
      0<dC = ineqLemma''' I oRing dAdC<0 dA<0
      have : (((numA * denomB) * denomC) + ((denomA * numC) * denomB)) < (((numB * denomA) * denomC) + ((denomA * numC) * denomB))
      have = OrderedRing.orderRespectsAddition oRing (ringCanMultiplyByPositive oRing 0<dC a<b) _
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inl (inr dA<0) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inl (inr dBdC<0) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inl (inr dAdC<0) | inr 0=dBdC with IntegralDomain.intDom I (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=dBdC)
  ... | inl x = exFalso (denomB!=0 x)
  ... | inr x = exFalso (denomC!=0 x)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inr (0=dAdC) with IntegralDomain.intDom I (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=dAdC)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inr 0=dAdC | inl x = exFalso (denomA!=0 x)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} a<b (numC ,, (denomC , denomC!=0)) | inr 0=dAdC | inr x = exFalso (denomC!=0 x)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} t u with SetoidTotalOrder.totality tOrder (Ring.0R R) (Ring.1R R)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) with SetoidTotalOrder.totality tOrder (Ring.0R R) (denomA * denomB)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) | inl (inl 0<dA) = SetoidPartialOrder.wellDefined pOrder (symmetric (transitive multCommutative (ringTimesZero R))) (symmetric (transitive multCommutative multIdentIsIdent)) 0<nAnB
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<nA : 0R < numA
      0<nA = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) (transitive multCommutative multIdentIsIdent) 0<a
      0<nB : 0R < numB
      0<nB = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) (transitive multCommutative multIdentIsIdent) 0<b
      0<nAnB : 0R < (numA * numB)
      0<nAnB = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) reflexive (ringCanMultiplyByPositive oRing 0<nB 0<nA)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) | inl (inr dA<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dAdB (SetoidPartialOrder.wellDefined pOrder multCommutative (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing dA<0 0<dB))))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inl 0<dB) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) | inl (inl 0<dA) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 0<dAdB (SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing dB<0 0<dA))))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) | inl (inr dA<0) = SetoidPartialOrder.wellDefined pOrder (symmetric (transitive multCommutative (ringTimesZero R))) (symmetric (transitive multCommutative multIdentIsIdent)) 0<nAnB
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      nB<0 : numB < 0R
      nB<0 = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative multIdentIsIdent) (transitive multCommutative (ringTimesZero R)) 0<b
      nA<0 : numA < 0R
      nA<0 = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative multIdentIsIdent) (transitive multCommutative (ringTimesZero R)) 0<a
      0<nAnB : 0R < (numA * numB)
      0<nAnB = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) multCommutative (ringCanMultiplyByNegative oRing nA<0 nB<0)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inl (inr dB<0) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inl 0<dAdB) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomB
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) | inl (inl 0<denomA) = exFalso f
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      f : False
      f with OrderedRing.orderRespectsMultiplication oRing 0<denomA 0<denomB
      ... | bl = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder bl dAdB<0)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) | inl (inr denomA<0) = SetoidPartialOrder.wellDefined pOrder (symmetric (transitive multCommutative multIdentIsIdent)) (symmetric (transitive multCommutative (ringTimesZero R))) ans
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      0<nB : 0R < numB
      0<nB = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) (transitive multCommutative multIdentIsIdent) 0<b
      nA<0 : numA < 0R
      nA<0 = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative multIdentIsIdent) (transitive multCommutative (ringTimesZero R)) 0<a
      ans : (numA * numB) < 0R
      ans = SetoidPartialOrder.wellDefined pOrder multCommutative (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing nA<0 0<nB)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inl 0<denomB) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) with SetoidTotalOrder.totality tOrder (Ring.0R R) denomA
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) | inl (inl 0<denomA) = SetoidPartialOrder.wellDefined pOrder (symmetric (transitive multCommutative multIdentIsIdent)) (symmetric (transitive multCommutative (ringTimesZero R))) nAnB<0
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      nB<0 : numB < 0R
      nB<0 = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative multIdentIsIdent) (transitive multCommutative (ringTimesZero R)) 0<b
      0<nA : 0R < numA
      0<nA = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) (transitive multCommutative multIdentIsIdent) 0<a
      nAnB<0 : (numA * numB) < 0R
      nAnB<0 = SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) (ringCanMultiplyByNegative oRing nB<0 0<nA)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) | inl (inr denomA<0) = exFalso f
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
      h : 0R < (denomA * denomB)
      h = SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) reflexive (ringCanMultiplyByNegative oRing denomB<0 denomA<0)
      f : False
      f = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder dAdB<0 h)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inl (inr denomB<0) | inr x = exFalso (denomA!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inl (inr dAdB<0) | inr x = exFalso (denomB!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inl 0<1) | inr 0=dAdB with IntegralDomain.intDom I (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=dAdB)
  ... | inl x = exFalso (denomA!=0 x)
  ... | inr x = exFalso (denomB!=0 x)
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inl (inr 1<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder 1<0 (SetoidPartialOrder.wellDefined pOrder (transitive multCommutative (ringTimesZero R)) multIdentIsIdent (ringCanMultiplyByNegative oRing 1<0 1<0))))
    where
      open Setoid S
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Ring R
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {S = S} {_+_} {_*_} {R} {_<_} {pOrder} {tOrder} I oRing) {numA ,, (denomA , denomA!=0)} {numB ,, (denomB , denomB!=0)} 0<a 0<b | inr x = exFalso (IntegralDomain.nontrivial I (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) x))
