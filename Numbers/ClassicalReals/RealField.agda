{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Fields.Fields
open import Rings.Orders.Total.Definition
open import Rings.Orders.Total.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Orders.LeastUpperBounds.Definition

module Numbers.ClassicalReals.RealField where

record RealField : Agda.Primitive.Setω where
  field
    a b c : _
    A : Set a
    S : Setoid {_} {b} A
    _+_ : A → A → A
    _*_ : A → A → A
    R : Ring S _+_ _*_
    nontrivial : Setoid._∼_ S (Ring.0R R) (Ring.1R R) → False
    F : Field R
    _<_ : Rel {_} {c} A
    pOrder : SetoidPartialOrder S _<_
    pOrderedRing : PartiallyOrderedRing R pOrder
    orderedRing : TotallyOrderedRing pOrderedRing
    lub : {d : _} → {pred : A → Set d} → (sub : subset S pred) → (nonempty : Sg A pred) → (boundedAbove : Sg A (UpperBound pOrder sub)) → Sg A (LeastUpperBound pOrder sub)
  open Setoid S
  charNot2 : (Ring.1R R + Ring.1R R) ∼ Ring.0R R → False
  charNot2 = orderedImpliesCharNot2 orderedRing nontrivial
