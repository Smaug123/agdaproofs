{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Homomorphisms.Definition
open import Groups.Lemmas
open import Groups.Homomorphisms.Lemmas

module Groups.Groups where

reflGroupWellDefined : {lvl : _} {A : Set lvl} {m n x y : A} {op : A → A → A} → m ≡ x → n ≡ y → (op m n) ≡ (op x y)
reflGroupWellDefined {lvl} {A} {m} {n} {.m} {.n} {op} refl refl = refl
fourWay+Associative : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → {r s t u : A} → (Setoid._∼_ S) (r · ((s · t) · u)) ((r · s) · (t · u))
fourWay+Associative {S = S} {_·_} G {r} {s} {t} {u} = transitive p1 (transitive p2 p3)
  where
    open Group G renaming (inverse to _^-1)
    open Setoid S
    open Equivalence eq
    p1 : r · ((s · t) · u) ∼ (r · (s · t)) · u
    p2 : (r · (s · t)) · u ∼ ((r · s) · t) · u
    p3 : ((r · s) · t) · u ∼ (r · s) · (t · u)
    p1 = Group.+Associative G
    p2 = Group.+WellDefined G (Group.+Associative G) reflexive
    p3 = symmetric (Group.+Associative G)

fourWay+Associative' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) {a b c d : A} → (Setoid._∼_ S (((a · b) · c) · d) (a · ((b · c) · d)))
fourWay+Associative' {S = S} G = transitive (symmetric +Associative) (symmetric (fourWay+Associative G))
  where
    open Group G
    open Setoid S
    open Equivalence eq

fourWay+Associative'' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) {a b c d : A} → (Setoid._∼_ S (a · (b · (c · d))) (a · ((b · c) · d)))
fourWay+Associative'' {S = S} {_·_ = _·_} G = transitive +Associative (symmetric (fourWay+Associative G))
  where
    open Group G
    open Setoid S
    open Equivalence eq

{-
quotientHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {f : A → B} → (fHom : GroupHom G H f) → A → A
quotientHom {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {f = f} fHom a = {!!}

quotientInjection : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {f : A → B} → (fHom : GroupHom G H f) → GroupHom (quotientGroup G fHom) G (quotientHom G fHom)
GroupHom.groupHom (quotientInjection {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {f = f} fHom) {x} {y} = {!!}
  where
    open Setoid S
    open Equivalence eq
    open Reflexive reflexiveEq
GroupHom.wellDefined (quotientInjection {S = S} {T = T} {_·A_ = _·A_} G {H = H} {f = f} fHom) {x} {y} x~y = {!!}
  where
    open Group G
    open Setoid S
    open Setoid T renaming (_∼_ to _∼T_)
    open Equivalence (Setoid.eq S)
    open Reflexive reflexiveEq
    have : f (x ·A inverse y) ∼T Group.0G H
    have = x~y
    need : x ∼ y
    need = {!!}

quotientIsSubgroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} → {f : A → B} → {fHom : GroupHom G H f} → Subgroup G (quotientGroup G fHom) (quotientInjection G fHom)
quotientIsSubgroup = {!!}

-}
