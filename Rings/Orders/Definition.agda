{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Orders.Definition {n m : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open Group additiveGroup
open Setoid S

record OrderedRing {p : _} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} (order : SetoidTotalOrder pOrder) : Set (lsuc n ⊔ m ⊔ p) where
  field
    orderRespectsAddition : {a b : A} → (a < b) → (c : A) → (a + c) < (b + c)
    orderRespectsMultiplication : {a b : A} → (0R < a) → (0R < b) → (0R < (a * b))
  open SetoidPartialOrder pOrder
  abs : A → A
  abs a with SetoidTotalOrder.totality order 0R a
  abs a | inl (inl 0<a) = a
  abs a | inl (inr a<0) = inverse a
  abs a | inr 0=a = a

  abstract
    absWellDefined : (a b : A) → a ∼ b → abs a ∼ abs b
    absWellDefined a b a=b with SetoidTotalOrder.totality order 0R a
    absWellDefined a b a=b | inl (inl 0<a) with SetoidTotalOrder.totality order 0R b
    absWellDefined a b a=b | inl (inl 0<a) | inl (inl 0<b) = a=b
    absWellDefined a b a=b | inl (inl 0<a) | inl (inr b<0) = exFalso (irreflexive {0G} (transitive 0<a (<WellDefined (Equivalence.symmetric eq a=b) (Equivalence.reflexive eq) b<0)))
    absWellDefined a b a=b | inl (inl 0<a) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq a=b (Equivalence.symmetric eq 0=b)) 0<a))
    absWellDefined a b a=b | inl (inr a<0) with SetoidTotalOrder.totality order 0R b
    absWellDefined a b a=b | inl (inr a<0) | inl (inl 0<b) = exFalso (irreflexive {0G} (transitive 0<b (<WellDefined a=b (Equivalence.reflexive eq) a<0)))
    absWellDefined a b a=b | inl (inr a<0) | inl (inr b<0) = inverseWellDefined additiveGroup a=b
    absWellDefined a b a=b | inl (inr a<0) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq a=b (Equivalence.symmetric eq 0=b)) (Equivalence.reflexive eq) a<0))
    absWellDefined a b a=b | inr 0=a with SetoidTotalOrder.totality order 0R b
    absWellDefined a b a=b | inr 0=a | inl (inl 0<b) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (Equivalence.transitive eq 0=a a=b)) 0<b))
    absWellDefined a b a=b | inr 0=a | inl (inr b<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq 0=a a=b)) (Equivalence.reflexive eq) b<0))
    absWellDefined a b a=b | inr 0=a | inr 0=b = a=b
