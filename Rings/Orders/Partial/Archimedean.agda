{-# OPTIONS --safe --warning=error --without-K #-}

open import Sets.EquivalenceRelations
open import Numbers.Naturals.Semiring
open import Numbers.Integers.Definition
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Groups.Definition
open import Rings.Orders.Partial.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Orders.Partial.Archimedean {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {_<_ : A → A → Set c} {pOrder : SetoidPartialOrder S _<_} (p : PartiallyOrderedRing R pOrder) where

open Setoid S
open Equivalence eq
open Ring R
open Group additiveGroup
open import Groups.Lemmas additiveGroup
open import Groups.Cyclic.Definition additiveGroup
open import Groups.Cyclic.DefinitionLemmas additiveGroup
open import Groups.Orders.Archimedean (toGroup R p)
open import Rings.Orders.Partial.Lemmas p
open import Rings.InitialRing R
open SetoidPartialOrder pOrder
open PartiallyOrderedRing p

ArchimedeanRing : Set (a ⊔ c)
ArchimedeanRing = (x : A) → Sg ℕ (λ n → x < (fromN n))

--archRingToGrp : ArchimedeanRing → Archimedean
--archRingToGrp a r s = {!!}

archGrpImpliesRing : Archimedean → ArchimedeanRing
archGrpImpliesRing a x with a 1R x
... | N , pr = N , pr
