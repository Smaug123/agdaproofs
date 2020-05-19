{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Orders.Archimedean
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Functions.Definition
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Fields.Orders.Total.Archimedean

module Fields.CauchyCompletion.Archimedean {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) (arch : ArchimedeanField {F = F} (record { oRing = pRing })) where

open import Fields.CauchyCompletion.Group order F
open import Fields.CauchyCompletion.Ring order F
open import Fields.CauchyCompletion.Comparison order F
open import Fields.CauchyCompletion.PartiallyOrderedRing order F

CArchimedean : Archimedean (toGroup CRing CpOrderedRing)
CArchimedean x y x₁ x₂ = {!!}
