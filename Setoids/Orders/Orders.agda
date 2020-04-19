{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Orders.Total.Definition
open import Orders.Partial.Definition
open import Setoids.Setoids
open import Functions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Setoids.Orders where

partialOrderToSetoidPartialOrder : {a b : _} {A : Set a} (P : PartialOrder {a} A {b}) → SetoidPartialOrder (reflSetoid A) (PartialOrder._<_ P)
SetoidPartialOrder.<WellDefined (partialOrderToSetoidPartialOrder P) a=b c=d a<c rewrite a=b | c=d = a<c
SetoidPartialOrder.irreflexive (partialOrderToSetoidPartialOrder P) = PartialOrder.irreflexive P
SetoidPartialOrder.<Transitive (partialOrderToSetoidPartialOrder P) = PartialOrder.<Transitive P

totalOrderToSetoidTotalOrder : {a b : _} {A : Set a} (T : TotalOrder {a} A {b}) → SetoidTotalOrder (partialOrderToSetoidPartialOrder (TotalOrder.order T))
SetoidTotalOrder.totality (totalOrderToSetoidTotalOrder T) = TotalOrder.totality T
