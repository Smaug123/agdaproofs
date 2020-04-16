{-# OPTIONS --safe --warning=error --without-K #-}

open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Setoids.Setoids
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions
open import Fields.Fields
open import Fields.Orders.Total.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.EquivalenceRelations
open import LogicalFormulae
open import Groups.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Orders.Total.Lemmas {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} {p : _} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} {oR : PartiallyOrderedRing R pOrder} (oF : TotallyOrderedField F oR) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open Field F
open TotallyOrderedField oF
open TotallyOrderedRing oRing
open PartiallyOrderedRing oR
open SetoidTotalOrder total
open SetoidPartialOrder pOrder
open import Rings.InitialRing R
open import Rings.Orders.Total.Lemmas oRing
open import Rings.Orders.Partial.Lemmas oR
open import Rings.Lemmas R
open import Groups.Lemmas additiveGroup

charNotN : (n : ℕ) → fromN (succ n) ∼ 0R → False
charNotN n pr = irreflexive (<WellDefined reflexive pr t)
  where
    t : 0R < fromN (succ n)
    t = fromNPreservesOrder (0<1 (Field.nontrivial F)) (succIsPositive n)

charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False
charNot2 pr = charNotN 1 (transitive (transitive +Associative identRight) pr)
