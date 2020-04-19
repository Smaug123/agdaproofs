{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.EuclideanDomains.Definition
open import Fields.Fields
open import Fields.Lemmas


module Rings.EuclideanDomains.Examples where

polynomialField : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) → (Setoid._∼_ S (Ring.1R R) (Ring.0R R) → False) → EuclideanDomain R
EuclideanDomain.isIntegralDomain (polynomialField F 1!=0) = fieldIsIntDom F
EuclideanDomain.norm (polynomialField F _) a!=0 = zero
EuclideanDomain.normSize (polynomialField F _) a!=0 b!=0 c b=ac = inr refl
DivisionAlgorithmResult.quotient (EuclideanDomain.divisionAlg (polynomialField {_*_ = _*_} F _) {a = a} {b} a!=0 b!=0) with Field.allInvertible F b b!=0
... | bInv , prB = a * bInv
DivisionAlgorithmResult.rem (EuclideanDomain.divisionAlg (polynomialField F _) a!=0 b!=0) = Field.0F F
DivisionAlgorithmResult.remSmall (EuclideanDomain.divisionAlg (polynomialField {S = S} F _) a!=0 b!=0) = inl (Equivalence.reflexive (Setoid.eq S))
DivisionAlgorithmResult.divAlg (EuclideanDomain.divisionAlg (polynomialField {S = S} {R = R} F _) {a = a} {b = b} a!=0 b!=0) with Field.allInvertible F b b!=0
... | bInv , prB = transitive (transitive (transitive (symmetric identIsIdent) (transitive *Commutative (*WellDefined reflexive (symmetric prB)))) *Associative) (symmetric identRight)
  where
    open Setoid S
    open Equivalence eq
    open Ring R
    open Group additiveGroup
