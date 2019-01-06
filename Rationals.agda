{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Naturals
open import Integers
open import Groups
open import Rings
open import Fields
open import PrimeNumbers
open import Setoids
open import Functions
open import FieldOfFractions

module Rationals where

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
