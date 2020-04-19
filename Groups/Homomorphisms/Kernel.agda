{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Subgroups.Definition
open import Groups.Subgroups.Normal.Definition
open import Groups.Lemmas


module Groups.Homomorphisms.Kernel {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) where

open Setoid T
open Equivalence eq

groupKernelPred : A → Set d
groupKernelPred a = Setoid._∼_ T (f a) (Group.0G H)

groupKernelPredWd : {x y : A} → (Setoid._∼_ S x y) → groupKernelPred x → groupKernelPred y
groupKernelPredWd x=y fx=0 = transitive (GroupHom.wellDefined fHom (Equivalence.symmetric (Setoid.eq S) x=y)) fx=0

groupKernelIsSubgroup : Subgroup G groupKernelPred
Subgroup.closedUnderPlus groupKernelIsSubgroup fg=0 fh=0 = transitive (transitive (GroupHom.groupHom fHom) (Group.+WellDefined H fg=0 fh=0)) (Group.identLeft H)
Subgroup.containsIdentity groupKernelIsSubgroup = imageOfIdentityIsIdentity fHom
Subgroup.closedUnderInverse groupKernelIsSubgroup fg=0 = transitive (homRespectsInverse fHom) (transitive (inverseWellDefined H fg=0) (invIdent H))
Subgroup.isSubset groupKernelIsSubgroup = groupKernelPredWd

groupKernelIsNormalSubgroup : normalSubgroup G groupKernelIsSubgroup
groupKernelIsNormalSubgroup {g} fk=0 = transitive (transitive (transitive (GroupHom.groupHom fHom) (transitive (Group.+WellDefined H reflexive (transitive (GroupHom.groupHom fHom) (transitive (Group.+WellDefined H fk=0 reflexive) (Group.identLeft H)))) (symmetric (GroupHom.groupHom fHom)))) (GroupHom.wellDefined fHom (Group.invRight G {g}))) (imageOfIdentityIsIdentity fHom)
