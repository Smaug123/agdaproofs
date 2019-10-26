{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Order
open import Groups.Definition
open import Groups.Groups
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals

module Fields.CauchyCompletion.Approximation {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder {_<_ = _<_} pOrder} {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Ring R
open Group additiveGroup
open Field F

open import Rings.Orders.Lemmas(order)
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Addition order F charNot2
open import Fields.CauchyCompletion.Setoid order F charNot2

approximate : (a : CauchyCompletion) → (ε : A) → Sg A (λ b → a +C (-C (injection b)) < ε)
approximate a ε = ?
