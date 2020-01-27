{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Fields.Fields
open import Setoids.Setoids
open import Sets.EquivalenceRelations


module Fields.FieldOfFractions.Field {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Ring I

fieldOfFractions : Field fieldOfFractionsRing
Field.allInvertible fieldOfFractions (fst ,, (b , _)) prA = (b ,, (fst , ans)) , need
  where
    abstract
      open Setoid S
      open Equivalence eq
      need : ((b * fst) * Ring.1R R) ∼ ((fst * b) * Ring.1R R)
      need = Ring.*WellDefined R (Ring.*Commutative R) reflexive
      ans : fst ∼ Ring.0R R → False
      ans pr = prA need'
        where
          need' : (fst * Ring.1R R) ∼ (b * Ring.0R R)
          need' = transitive (Ring.*WellDefined R pr reflexive) (transitive (transitive (Ring.*Commutative R) (Ring.timesZero R)) (symmetric (Ring.timesZero R)))
Field.nontrivial fieldOfFractions pr = IntegralDomain.nontrivial I (symmetric (transitive (symmetric (Ring.timesZero R)) (transitive (Ring.*Commutative R) (transitive pr (Ring.identIsIdent R)))))
  where
    open Setoid S
    open Equivalence eq
    pr' : (Ring.0R R) * (Ring.1R R) ∼ (Ring.1R R) * (Ring.1R R)
    pr' = pr
