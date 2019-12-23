{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Rings.IntegralDomains.Definition
open import Rings.IntegralDomains.Examples
open import Rings.EuclideanDomains.Definition
open import Fields.Fields
open import WellFoundedInduction

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.EuclideanDomains.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (E : EuclideanDomain R) where

open import Rings.PrincipalIdealDomains.Definition (EuclideanDomain.isIntegralDomain E)
open import Rings.Ideals.Principal.Definition R
open import Rings.Divisible.Definition R
open Setoid S
open Ring R
open Equivalence eq

euclideanDomainIsPid : {c : _} → PrincipalIdealDomain {c}
euclideanDomainIsPid {pred = pred} ideal = {!!}
-- We definitely need to be able to decide equality in order to deduce this; otherwise we can't tell the difference
-- between "everything is 0" and "something is nonzero", and the proofs are genuinely different in the two cases.
  where
    r : A
    r = {!!}
    r!=0 : (r ∼ 0R) → False
    r!=0 = {!!}
    predR : pred r
    predR = {!!}
    sr : (s : A) → r ∣ s
    sr = EuclideanDomain.divisionAlg r!=0 s!=0 ?
