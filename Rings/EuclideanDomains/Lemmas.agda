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

open import Rings.PrincipalIdealDomain

euclideanDomainIsPid : {c : _} → PrincipalIdealDomain R {c}
euclideanDomainIsPid ideal = {!!}
