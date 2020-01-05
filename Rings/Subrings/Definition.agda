{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Subrings.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ _*A_ : A → A → A} (R : Ring S _+A_ _*A_) where

open import Setoids.Subset S
open Ring R
open Group additiveGroup
open import Groups.Subgroups.Definition additiveGroup
open Setoid S
open Equivalence eq

record Subring {c : _} (pred : A → Set c) : Set (a ⊔ b ⊔ c) where
  field
    isSubgroup : Subgroup pred
    containsOne : pred 1R
    closedUnderProduct : {x y : A} → pred x → pred y → pred (x *A y)
  isSubset = Subgroup.isSubset isSubgroup

subringMult : {c : _} {pred : A → Set c} → (s : Subring pred) → Sg A pred → Sg A pred → Sg A pred
subringMult s (a , prA) (b , prB) = (a *A b) , Subring.closedUnderProduct s prA prB

subringIsRing : {c : _} {pred : A → Set c} → (subring : Subring pred) → Ring (subsetSetoid (Subring.isSubset subring)) (subgroupOp (Subring.isSubgroup subring)) (subringMult subring)
Ring.additiveGroup (subringIsRing sub) = subgroupIsGroup (Subring.isSubgroup sub)
Ring.*WellDefined (subringIsRing sub) {r , prR} {s , prS} {t , prT} {u , prU} r=t s=u = *WellDefined r=t s=u
Ring.1R (subringIsRing sub) = (1R , Subring.containsOne sub)
Ring.groupIsAbelian (subringIsRing sub) {a , prA} {b , prB} = groupIsAbelian
Ring.*Associative (subringIsRing sub) {a , prA} {b , prB} {c , prC} = *Associative
Ring.*Commutative (subringIsRing sub) {a , prA} {b , prB} = *Commutative
Ring.*DistributesOver+ (subringIsRing sub) {a , prA} {b , prB} {c , prC} = *DistributesOver+
Ring.identIsIdent (subringIsRing sub) {a , prA} = identIsIdent
