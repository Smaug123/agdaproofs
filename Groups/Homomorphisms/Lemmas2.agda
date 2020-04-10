{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Homomorphisms.Lemmas2 {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ : A → A → A} (G : Group S _+A_) where

imageGroup : {c d : _} {B : Set c} {T : Setoid {c} {d} B} {_+B_ : B → B → B} → (f : A → B) → SetoidSurjection S T f → ({x y : A} → Setoid._∼_ T (f (x +A y)) ((f x) +B (f y))) → ({x y m n : B} → Setoid._∼_ T x m → Setoid._∼_ T y n → Setoid._∼_ T (x +B y) (m +B n)) → Group T _+B_
Group.+WellDefined (imageGroup f surj respects+ wd) {m} {n} {x} {y} = wd
Group.0G (imageGroup f surj respects+ wd) = f (Group.0G G)
Group.inverse (imageGroup f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) b with surjective {b}
Group.inverse (imageGroup f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) b | a , fa=b = f (Group.inverse G a)
Group.+Associative (imageGroup {T = T} f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) {a} {b} {c} with surjective {a}
... | x , fx=a with surjective {b}
... | y , fy=b with surjective {c}
... | z , fz=c = transitive (wd (symmetric fx=a) (transitive (wd (symmetric fy=b) (symmetric fz=c)) (symmetric respects+))) (transitive (transitive (symmetric respects+) (transitive (wellDefined (Group.+Associative G)) respects+)) (wd (transitive respects+ (wd fx=a fy=b)) fz=c))
  where
    open Setoid T
    open Equivalence eq
Group.identRight (imageGroup {T = T} f record { wellDefined = wd ; surjective = surjective } respects+ bWd) {b} with surjective {b}
... | a , fa=b = transitive (bWd (symmetric fa=b) reflexive) (transitive (symmetric respects+) (transitive (wd (Group.identRight G)) fa=b))
  where
    open Setoid T
    open Equivalence eq
Group.identLeft (imageGroup {T = T} f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) {b} with surjective {b}
... | a , fa=b = transitive (wd reflexive (symmetric fa=b)) (transitive (symmetric respects+) (transitive (wellDefined (Group.identLeft G)) fa=b))
  where
    open Setoid T
    open Equivalence eq
Group.invLeft (imageGroup {T = T} f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) {b} with surjective {b}
Group.invLeft (imageGroup {T = T} f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) {b} | a , fa=b = transitive (wd reflexive (symmetric fa=b)) (transitive (symmetric respects+) (wellDefined (Group.invLeft G)))
  where
    open Setoid T
    open Equivalence eq
Group.invRight (imageGroup f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) {b} with surjective {b}
Group.invRight (imageGroup {T = T} f record { wellDefined = wellDefined ; surjective = surjective } respects+ wd) {b} | a , fa=b = transitive (wd (symmetric fa=b) reflexive) (transitive (symmetric respects+) (wellDefined (Group.invRight G)))
  where
    open Setoid T
    open Equivalence eq

homToImageGroup : {c d : _} {B : Set c} {T : Setoid {c} {d} B} {_+B_ : B → B → B} → (f : A → B) → (surj : SetoidSurjection S T f) → (respects+ : {x y : A} → Setoid._∼_ T (f (x +A y)) ((f x) +B (f y))) → (wd : {x y m n : B} → Setoid._∼_ T x m → Setoid._∼_ T y n → Setoid._∼_ T (x +B y) (m +B n)) → GroupHom G (imageGroup f surj respects+ wd) f
GroupHom.groupHom (homToImageGroup f surj respects+ wd) = respects+
GroupHom.wellDefined (homToImageGroup f surj respects+ wd) = SetoidSurjection.wellDefined surj
