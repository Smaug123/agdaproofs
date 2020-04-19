{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Functions.Definition
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Homomorphisms.Definition
open import Groups.Lemmas

module Groups.Homomorphisms.Lemmas {a b c d : _} {A : Set a} {S : Setoid {a} {c} A} {B : Set b} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (hom : GroupHom G H f) where

imageOfIdentityIsIdentity : Setoid._∼_ T (f (Group.0G G)) (Group.0G H)
imageOfIdentityIsIdentity = Equivalence.symmetric (Setoid.eq T) t
  where
    open Group H
    open Setoid T
    id2 : Setoid._∼_ S (Group.0G G) ((Group.0G G) +A (Group.0G G))
    id2 = Equivalence.symmetric (Setoid.eq S) (Group.identRight G)
    r : f (Group.0G G) ∼ f (Group.0G G) +B f (Group.0G G)
    s : 0G +B f (Group.0G G) ∼ f (Group.0G G) +B f (Group.0G G)
    t : 0G ∼ f (Group.0G G)
    t = groupsHaveRightCancellation H (f (Group.0G G)) 0G (f (Group.0G G)) s
    s = Equivalence.transitive (Setoid.eq T) identLeft r
    r = Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined hom id2) (GroupHom.groupHom hom)

groupHomsCompose : {o t : _} {C : Set o} {U : Setoid {o} {t} C} {_+C_ : C → C → C} {I : Group U _+C_} {g : B → C} (gHom : GroupHom H I g) → GroupHom G I (g ∘ f)
GroupHom.wellDefined (groupHomsCompose {I} {f} gHom) {x} {y} pr = GroupHom.wellDefined gHom (GroupHom.wellDefined hom pr)
GroupHom.groupHom (groupHomsCompose {U = U} {_+C_ = _·C_} {I} {g} gHom) {x} {y} = answer
  where
    open Group I
    answer : (Setoid._∼_ U) ((g ∘ f) (x +A y)) ((g ∘ f) x ·C (g ∘ f) y)
    answer = (Equivalence.transitive (Setoid.eq U)) (GroupHom.wellDefined gHom (GroupHom.groupHom hom {x} {y}) ) (GroupHom.groupHom gHom {f x} {f y})

homRespectsInverse : {x : A} → Setoid._∼_ T (f (Group.inverse G x)) (Group.inverse H (f x))
homRespectsInverse {x} = rightInversesAreUnique H {f x} {f (Group.inverse G x)} (transitive (symmetric (GroupHom.groupHom hom)) (transitive (GroupHom.wellDefined hom (Group.invLeft G)) imageOfIdentityIsIdentity))
  where
    open Setoid T
    open Equivalence eq

zeroImpliesInverseZero : {x : A} → Setoid._∼_ T (f x) (Group.0G H) → Setoid._∼_ T (f (Group.inverse G x)) (Group.0G H)
zeroImpliesInverseZero {x} fx=0 = transitive homRespectsInverse (transitive (inverseWellDefined H fx=0) (invIdent H))
  where
    open Setoid T
    open Equivalence eq

homRespectsInverse' : {a b : A} → Setoid._∼_ T (f (Group.inverse G a) +B f (Group.inverse G b)) (Group.inverse H (f (b +A a)))
homRespectsInverse' {a} {b} = transitive (symmetric (GroupHom.groupHom hom)) (transitive (GroupHom.wellDefined hom (Equivalence.symmetric (Setoid.eq S) (invContravariant G))) (homRespectsInverse))
  where
    open Setoid T
    open Equivalence eq
