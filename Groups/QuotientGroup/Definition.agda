{-# OPTIONS --warning=error --safe --without-K #-}

open import Groups.Definition
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Groups.Lemmas
open import Groups.Homomorphisms.Lemmas

module Groups.QuotientGroup.Definition {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (fHom : GroupHom G H f) where

quotientGroupSetoid : (Setoid {a} {d} A)
quotientGroupSetoid = ansSetoid
  where
    open Setoid T
    open Group H
    open Equivalence eq
    ansSetoid : Setoid A
    Setoid._∼_ ansSetoid r s = (f (r ·A (Group.inverse G s))) ∼ 0G
    Equivalence.reflexive (Setoid.eq ansSetoid) {b} = transitive (GroupHom.wellDefined fHom (Group.invRight G)) (imageOfIdentityIsIdentity fHom)
    Equivalence.symmetric (Setoid.eq ansSetoid) {m} {n} pr = i
      where
        g : f (Group.inverse G (m ·A Group.inverse G n)) ∼ 0G
        g = transitive (homRespectsInverse fHom {m ·A Group.inverse G n}) (transitive (inverseWellDefined H pr) (invIdent H))
        h : f (Group.inverse G (Group.inverse G n) ·A Group.inverse G m) ∼ 0G
        h = transitive (GroupHom.wellDefined fHom (Equivalence.symmetric (Setoid.eq S) (invContravariant G))) g
        i : f (n ·A Group.inverse G m) ∼ 0G
        i = transitive (GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.symmetric (Setoid.eq S) (invTwice G n)) (Equivalence.reflexive (Setoid.eq S)))) h
    Equivalence.transitive (Setoid.eq ansSetoid) {m} {n} {o} prmn prno = transitive (GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.reflexive (Setoid.eq S)) (Equivalence.symmetric (Setoid.eq S) (Group.identLeft G)))) k
      where
        g : f (m ·A Group.inverse G n) ·B f (n ·A Group.inverse G o) ∼ 0G ·B 0G
        g = replaceGroupOp H reflexive reflexive prmn prno reflexive
        h : f (m ·A Group.inverse G n) ·B f (n ·A Group.inverse G o) ∼ 0G
        h = transitive g identLeft
        i : f ((m ·A Group.inverse G n) ·A (n ·A Group.inverse G o)) ∼ 0G
        i = transitive (GroupHom.groupHom fHom) h
        j : f (m ·A (((Group.inverse G n) ·A n) ·A Group.inverse G o)) ∼ 0G
        j = transitive (GroupHom.wellDefined fHom (fourWay+Associative G)) i
        k : f (m ·A ((Group.0G G) ·A Group.inverse G o)) ∼ 0G
        k = transitive (GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.reflexive (Setoid.eq S)) (Group.+WellDefined G (Equivalence.symmetric (Setoid.eq S) (Group.invLeft G)) (Equivalence.reflexive (Setoid.eq S))))) j


quotientGroupByHom : Group (quotientGroupSetoid) _·A_
Group.+WellDefined (quotientGroupByHom) {x} {y} {m} {n} x~m y~n = ans
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
Group.0G (quotientGroupByHom) = Group.0G G
Group.inverse (quotientGroupByHom) = Group.inverse G
Group.+Associative (quotientGroupByHom) {a} {b} {c} = ans
  where
    open Setoid T
    open Equivalence (Setoid.eq T)
    ans : f ((a ·A (b ·A c)) ·A (Group.inverse G ((a ·A b) ·A c))) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transferToRight'' G (Group.+Associative G))) (imageOfIdentityIsIdentity fHom)
Group.identRight (quotientGroupByHom) {a} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    transitiveG = Equivalence.transitive (Setoid.eq S)
    ans : f ((a ·A 0G) ·A inverse a) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.+WellDefined G (Group.identRight G) (Equivalence.reflexive (Setoid.eq S))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
Group.identLeft (quotientGroupByHom) {a} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    transitiveG = Equivalence.transitive (Setoid.eq S)
    ans : f ((0G ·A a) ·A (inverse a)) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.+WellDefined G (Group.identLeft G) (Equivalence.reflexive (Setoid.eq S))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
Group.invLeft (quotientGroupByHom) {x} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    ans : f ((inverse x ·A x) ·A (inverse 0G)) ∼ (Group.0G H)
    ans = transitive (GroupHom.wellDefined fHom (Equivalence.transitive (Setoid.eq S) (replaceGroupOp G (Equivalence.symmetric (Setoid.eq S) (Group.invLeft G)) (Equivalence.symmetric (Setoid.eq S) (invIdent G)) (Equivalence.reflexive (Setoid.eq S)) ((Equivalence.reflexive (Setoid.eq S))) ((Equivalence.reflexive (Setoid.eq S)))) (identRight {0G}))) (imageOfIdentityIsIdentity fHom)
Group.invRight (quotientGroupByHom) {x} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    ans : f ((x ·A inverse x) ·A (inverse 0G)) ∼ (Group.0G H)
    ans = transitive (GroupHom.wellDefined fHom (Equivalence.transitive (Setoid.eq S) (replaceGroupOp G (Equivalence.symmetric (Setoid.eq S) (Group.invRight G)) (Equivalence.symmetric (Setoid.eq S) (invIdent G)) (Equivalence.reflexive (Setoid.eq S)) (Equivalence.reflexive (Setoid.eq S)) (Equivalence.reflexive (Setoid.eq S))) (identRight {0G}))) (imageOfIdentityIsIdentity fHom)
