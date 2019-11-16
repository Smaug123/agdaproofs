{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Abelian.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Groups.Abelian.Definition
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Integers
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Modules.Definition
open import Groups.Cyclic.Definition
open import Groups.Cyclic.DefinitionLemmas

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Modules.Examples where

abGrpModule : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {G' : Group S _+_} (G : AbelianGroup G') → Module ℤRing G (λ x i → elementPower G' i x)
Module.dotWellDefined (abGrpModule {S = S} {G' = G'} G) {m} {n} {g} {h} m=n g=h = transitive (elementPowerWellDefinedG G' g h g=h {m}) (elementPowerWellDefinedZ' G' m n m=n {h})
  where
    open Setoid S
    open Equivalence eq
Module.dotDistributesLeft (abGrpModule {G' = G'} G) {n} {x} {y} = elementPowerHomAbelian G' (AbelianGroup.commutative G) x y n
Module.dotDistributesRight (abGrpModule {S = S} {G' = G'} G) {r} {s} {x} = symmetric (elementPowerCollapse G' x r s)
  where
    open Equivalence (Setoid.eq S)
Module.dotAssociative (abGrpModule {G' = G'} G) {r} {s} {x} = elementPowerMultiplies G' r s x
Module.dotIdentity (abGrpModule {G' = G'} G) = Group.identRight G'
