{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Groups.Abelian.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Modules.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Modules.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+R_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+R_ _*_} {m n : _} {M : Set m} {T : Setoid {m} {n} M} {_+_ : M → M → M} {G' : Group T _+_} {G : AbelianGroup G'} {_·_ : A → M → M} (mod : Module R G _·_) where

open Group G'
open Ring R
open Setoid T
open Equivalence eq
open Module mod

moduleTimesZero : {x : M} → (0R · x) ∼ 0G
moduleTimesZero {x} = equalsDoubleImpliesZero G' (symmetric x=2x)
  where
    x=2x : (0R · x) ∼ (0R · x) + (0R · x)
    x=2x = transitive (dotWellDefined (Equivalence.symmetric (Setoid.eq S) (Group.identLeft additiveGroup)) reflexive) dotDistributesRight

moduleTimes-1 : {x : M} → ((Group.inverse additiveGroup 1R) · x) ∼ inverse x
moduleTimes-1 {x} = transitive (transferToRight' G' j) (inverseWellDefined G' dotIdentity)
  where
    i : ((1R · x) + ((Group.inverse additiveGroup 1R) · x)) ∼ 0G
    i = transitive (symmetric (transitive (dotWellDefined (Equivalence.symmetric (Setoid.eq S) (Group.invRight additiveGroup {1R})) reflexive) dotDistributesRight)) (moduleTimesZero)
    j : (((Group.inverse additiveGroup 1R) · x) + (1R · x)) ∼ 0G
    j = transitive (AbelianGroup.commutative G) i
