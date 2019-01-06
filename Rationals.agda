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

  ℚ : Field'
  ℚ = encapsulateField (fieldOfFractions ℤIntDom)
