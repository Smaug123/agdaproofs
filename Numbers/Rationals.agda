{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals
open import Numbers.Integers
open import Groups.Groups
open import Rings.RingDefinition
open import Fields.Fields
open import PrimeNumbers
open import Setoids.Setoids
open import Functions
open import Fields.FieldOfFractions

module Numbers.Rationals where

  ℚ : Set
  ℚ = fieldOfFractionsSet ℤIntDom

  _+Q_ : ℚ → ℚ → ℚ
  a +Q b = fieldOfFractionsPlus ℤIntDom a b

  _*Q_ : ℚ → ℚ → ℚ
  a *Q b = fieldOfFractionsTimes ℤIntDom a b

  ℚRing : Ring (fieldOfFractionsSetoid ℤIntDom) _+Q_ _*Q_
  ℚRing = fieldOfFractionsRing ℤIntDom

  ℚField : Field ℚRing
  ℚField = fieldOfFractions ℤIntDom

  ℚField : OrderedRing ℚRing (fieldOfFractionsTotalOrder ℤIntDom ℤOrderedRing)
  ℚField = fieldOfFractionsOrderedRing ℤIntDom ℤOrderedRing
