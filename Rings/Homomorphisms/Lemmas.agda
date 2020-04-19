{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Setoids
open import Functions.Definition
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Homomorphisms.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ _*A_ : A → A → A} (R : Ring S _+A_ _*A_) where

open import Groups.Homomorphisms.Lemmas2 (Ring.additiveGroup R)

imageRing : {c d : _} {B : Set c} {T : Setoid {c} {d} B} {_+B_ : B → B → B} {_*B_ : B → B → B} → (f : A → B) → SetoidSurjection S T f → ({x y : A} → Setoid._∼_ T (f (x +A y)) ((f x) +B (f y))) → ({x y : A} → Setoid._∼_ T (f (x *A y)) ((f x) *B (f y))) → ({x y m n : B} → Setoid._∼_ T x m → Setoid._∼_ T y n → Setoid._∼_ T (x +B y) (m +B n)) → ({x y m n : B} → Setoid._∼_ T x m → Setoid._∼_ T y n → Setoid._∼_ T (x *B y) (m *B n)) → Ring T _+B_ _*B_
Ring.additiveGroup (imageRing f surj respects+ respects* +wd *wd) = imageGroup f surj respects+ +wd
Ring.*WellDefined (imageRing f surj respects+ respects* +wd *wd) = *wd
Ring.1R (imageRing f surj respects+ respects* +wd *wd) = f (Ring.1R R)
Ring.groupIsAbelian (imageRing {T = T} f record { surjective = surjective ; wellDefined = wellDefined } respects+ respects* +wd *wd) {a} {b} with surjective {a}
... | x , fx=a with surjective {b}
... | y , fy=b = transitive (+wd (symmetric fx=a) (symmetric fy=b)) (transitive (transitive (symmetric respects+) (transitive (wellDefined (Ring.groupIsAbelian R)) respects+)) (+wd fy=b fx=a))
  where
    open Setoid T
    open Equivalence eq
Ring.*Associative (imageRing {T = T} f record { surjective = surjective ; wellDefined = wellDefined } respects+ respects* +wd *wd) {a} {b} {c} with surjective {a}
... | x , fx=a with surjective {b}
... | y , fy=b with surjective {c}
... | z , fz=c = transitive (*wd (symmetric fx=a) (transitive (*wd (symmetric fy=b) (symmetric fz=c)) (symmetric respects*))) (transitive (transitive (symmetric respects*) (transitive (wellDefined (Ring.*Associative R)) respects*)) (*wd (transitive respects* (*wd fx=a fy=b)) fz=c))
  where
    open Setoid T
    open Equivalence eq
Ring.*Commutative (imageRing {T = T} f record { surjective = surjective ; wellDefined = wellDefined } respects+ respects* +wd *wd) {a} {b} with surjective {a}
... | x , fx=a with surjective {b}
... | y , fy=b = transitive (*wd (symmetric fx=a) (symmetric fy=b)) (transitive (transitive (symmetric respects*) (transitive (wellDefined (Ring.*Commutative R)) respects*)) (*wd fy=b fx=a))
  where
    open Setoid T
    open Equivalence eq
Ring.*DistributesOver+ (imageRing {T = T} f record { surjective = surjective ; wellDefined = wellDefined } respects+ respects* +wd *wd) {a} {b} {c} with surjective {a}
... | x , fx=a with surjective {b}
... | y , fy=b with surjective {c}
... | z , fz=c = transitive (*wd (symmetric fx=a) (+wd (symmetric fy=b) (symmetric fz=c))) (transitive (transitive (transitive (*wd reflexive (symmetric respects+)) (symmetric respects*)) (transitive (transitive (wellDefined (Ring.*DistributesOver+ R)) respects+) (+wd respects* respects*))) (+wd (*wd fx=a fy=b) (*wd fx=a fz=c)))
  where
    open Setoid T
    open Equivalence eq
Ring.identIsIdent (imageRing {T = T} f record { wellDefined = wellDefined ; surjective = surjective } respects+ respects* +wd *wd) {b} with surjective {b}
Ring.identIsIdent (imageRing {T = T} f record { wellDefined = wellDefined ; surjective = surjective } respects+ respects* +wd *wd) {b} | a , fa=b = transitive (transitive (*wd reflexive (symmetric fa=b)) (transitive (symmetric respects*) (wellDefined (Ring.identIsIdent R)))) fa=b
  where
    open Setoid T
    open Equivalence eq

homToImageRing : {c d : _} {B : Set c} {T : Setoid {c} {d} B} {_+B_ : B → B → B} {_*B_ : B → B → B} → (f : A → B) → (surj : SetoidSurjection S T f) → (respects+ : {x y : A} → Setoid._∼_ T (f (x +A y)) ((f x) +B (f y))) → (respects* : {x y : A} → Setoid._∼_ T (f (x *A y)) ((f x) *B (f y))) → (+wd : {x y m n : B} → Setoid._∼_ T x m → Setoid._∼_ T y n → Setoid._∼_ T (x +B y) (m +B n)) → (*wd : {x y m n : B} → Setoid._∼_ T x m → Setoid._∼_ T y n → Setoid._∼_ T (x *B y) (m *B n)) → RingHom R (imageRing f surj respects+ respects* +wd *wd) f
RingHom.preserves1 (homToImageRing {T = T} f surj respects+ respects* +wd *wd) = reflexive
  where
    open Setoid T
    open Equivalence eq
RingHom.ringHom (homToImageRing f surj respects+ respects* +wd *wd) = respects*
RingHom.groupHom (homToImageRing f surj respects+ respects* +wd *wd) = homToImageGroup f surj respects+ +wd
