{-# OPTIONS --warning=error --safe --without-K #-}

open import Functions
open import Sets.FinSet
open import LogicalFormulae
open import Groups.Definition
open import Groups.Groups
open import Groups.FiniteGroups.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Abelian.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Fields.FieldOfFractions.Setoid
open import Sets.EquivalenceRelations
open import Groups.Lemmas
open import Groups.Homomorphisms.Lemmas
open import Groups.Subgroups.Definition
open import Groups.Subgroups.Normal.Definition

module Groups.QuotientGroup.Definition where

quotientGroupByHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {underf : A → B} → (f : GroupHom G H underf) → Group (quotientGroupSetoid G f) _·A_
Group.+WellDefined (quotientGroupByHom {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {H = H} {underf = f} fHom) {x} {y} {m} {n} x~m y~n = ans
  where
    open Setoid T
    open Equivalence (Setoid.eq T)
    p1 : f ((x ·A y) ·A (Group.inverse G (m ·A n))) ∼ f ((x ·A y) ·A ((Group.inverse G n) ·A (Group.inverse G m)))
    p2 : f ((x ·A y) ·A ((Group.inverse G n) ·A (Group.inverse G m))) ∼ f (x ·A ((y ·A (Group.inverse G n)) ·A (Group.inverse G m)))
    p3 : f (x ·A ((y ·A (Group.inverse G n)) ·A (Group.inverse G m))) ∼ (f x) ·B f ((y ·A (Group.inverse G n)) ·A (Group.inverse G m))
    p4 : (f x) ·B f ((y ·A (Group.inverse G n)) ·A (Group.inverse G m)) ∼ (f x) ·B (f (y ·A (Group.inverse G n)) ·B f (Group.inverse G m))
    p5 : (f x) ·B (f (y ·A (Group.inverse G n)) ·B f (Group.inverse G m)) ∼ (f x) ·B (Group.0G H ·B f (Group.inverse G m))
    p6 : (f x) ·B (Group.0G H ·B f (Group.inverse G m)) ∼ (f x) ·B f (Group.inverse G m)
    p7 : (f x) ·B f (Group.inverse G m) ∼ f (x ·A (Group.inverse G m))
    p8 : f (x ·A (Group.inverse G m)) ∼ Group.0G H
    p1 = GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.reflexive (Setoid.eq S)) (invContravariant G))
    p2 = GroupHom.wellDefined fHom (Equivalence.symmetric (Setoid.eq S) (fourWay+Associative G))
    p3 = GroupHom.groupHom fHom
    p4 = Group.+WellDefined H reflexive (GroupHom.groupHom fHom)
    p5 = Group.+WellDefined H reflexive (replaceGroupOp H (symmetric y~n) reflexive reflexive reflexive reflexive)
    p6 = Group.+WellDefined H reflexive (Group.identLeft H)
    p7 = symmetric (GroupHom.groupHom fHom)
    p8 = x~m
    ans : f ((x ·A y) ·A (Group.inverse G (m ·A n))) ∼ Group.0G H
    ans = transitive p1 (transitive p2 (transitive p3 (transitive p4 (transitive p5 (transitive p6 (transitive p7 p8))))))
Group.0G (quotientGroupByHom G fHom) = Group.0G G
Group.inverse (quotientGroupByHom G fHom) = Group.inverse G
Group.+Associative (quotientGroupByHom {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} {b} {c} = ans
  where
    open Setoid T
    open Equivalence (Setoid.eq T)
    ans : f ((a ·A (b ·A c)) ·A (Group.inverse G ((a ·A b) ·A c))) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transferToRight'' G (Group.+Associative G))) (imageOfIdentityIsIdentity fHom)
Group.identRight (quotientGroupByHom {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    transitiveG = Equivalence.transitive (Setoid.eq S)
    ans : f ((a ·A 0G) ·A inverse a) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.+WellDefined G (Group.identRight G) (Equivalence.reflexive (Setoid.eq S))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
Group.identLeft (quotientGroupByHom {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    transitiveG = Equivalence.transitive (Setoid.eq S)
    ans : f ((0G ·A a) ·A (inverse a)) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.+WellDefined G (Group.identLeft G) (Equivalence.reflexive (Setoid.eq S))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
Group.invLeft (quotientGroupByHom {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {x} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    ans : f ((inverse x ·A x) ·A (inverse 0G)) ∼ (Group.0G H)
    ans = transitive (GroupHom.wellDefined fHom (Equivalence.transitive (Setoid.eq S) (replaceGroupOp G (Equivalence.symmetric (Setoid.eq S) (Group.invLeft G)) (Equivalence.symmetric (Setoid.eq S) (invIdent G)) (Equivalence.reflexive (Setoid.eq S)) ((Equivalence.reflexive (Setoid.eq S))) ((Equivalence.reflexive (Setoid.eq S)))) (identRight {0G}))) (imageOfIdentityIsIdentity fHom)
Group.invRight (quotientGroupByHom {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {x} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    ans : f ((x ·A inverse x) ·A (inverse 0G)) ∼ (Group.0G H)
    ans = transitive (GroupHom.wellDefined fHom (Equivalence.transitive (Setoid.eq S) (replaceGroupOp G (Equivalence.symmetric (Setoid.eq S) (Group.invRight G)) (Equivalence.symmetric (Setoid.eq S) (invIdent G)) (Equivalence.reflexive (Setoid.eq S)) (Equivalence.reflexive (Setoid.eq S)) (Equivalence.reflexive (Setoid.eq S))) (identRight {0G}))) (imageOfIdentityIsIdentity fHom)
