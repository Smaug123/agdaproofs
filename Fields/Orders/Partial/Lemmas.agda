{-# OPTIONS --safe --warning=error --without-K #-}

open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Fields.Fields
open import Fields.Orders.Partial.Definition
open import Numbers.Naturals.Semiring
open import Sets.EquivalenceRelations
open import LogicalFormulae
open import Groups.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Orders.Partial.Lemmas {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} {p : _} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} (oF : PartiallyOrderedField F pOrder) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open Field F
open PartiallyOrderedField oF
open SetoidPartialOrder pOrder
open import Rings.Orders.Partial.Lemmas oRing
open import Rings.InitialRing R

