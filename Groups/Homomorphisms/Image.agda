{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Setoids
open import Setoids.Subset
open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Subgroups.Definition
open import Groups.Lemmas

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Homomorphisms.Image {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) where

imageGroupPred : B → Set (a ⊔ d)
imageGroupPred b = Sg A (λ a → Setoid._∼_ T (f a) b)

imageGroupSubset : subset T imageGroupPred
imageGroupSubset {x} {y} x=y (a , fa=x) = a , transitive fa=x x=y
  where
    open Setoid T
    open Equivalence eq

imageGroupSubgroup : Subgroup H imageGroupPred
Subgroup.isSubset imageGroupSubgroup = imageGroupSubset
Subgroup.closedUnderPlus imageGroupSubgroup {x} {y} (a , fa=x) (b , fb=y) = (a +A b) , transitive (GroupHom.groupHom fHom) (Group.+WellDefined H fa=x fb=y)
  where
    open Setoid T
    open Equivalence eq
Subgroup.containsIdentity imageGroupSubgroup = Group.0G G , imageOfIdentityIsIdentity fHom
Subgroup.closedUnderInverse imageGroupSubgroup {x} (a , fa=x) = Group.inverse G a , transitive (homRespectsInverse fHom) (inverseWellDefined H fa=x)
  where
    open Setoid T
    open Equivalence eq
