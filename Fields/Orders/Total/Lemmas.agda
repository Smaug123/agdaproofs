{-# OPTIONS --safe --warning=error --without-K #-}

open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Setoids.Setoids
open import Setoids.Orders
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

1/nPositive : (n : ℕ) → (charNotN : (fromN (succ n) ∼ 0R) → False) → 0R < underlying (allInvertible _ charNotN)
1/nPositive 0 nNot0 with allInvertible (fromN 1) nNot0
... | 1/1 , pr1 = <WellDefined reflexive (transitive (symmetric pr1) (transitive (transitive (*WellDefined reflexive identRight) *Commutative) identIsIdent)) (0<1 λ i → nNot0 (transitive identRight (symmetric i)))
1/nPositive (succ n) nNot0 with allInvertible (fromN (succ (succ n))) nNot0
... | 1/n , pr1/n with totality 0R 1/n
... | inr x = exFalso (nNot0 (oneZeroImpliesAllZero (transitive (symmetric (transitive (*WellDefined (symmetric x) reflexive) timesZero')) pr1/n)))
... | inl (inl x) = x
... | inl (inr x) = exFalso (1<0False (<WellDefined pr1/n timesZero' (ringCanMultiplyByPositive (fromNPreservesOrder (anyComparisonImpliesNontrivial x) (succIsPositive (succ n))) x)))
