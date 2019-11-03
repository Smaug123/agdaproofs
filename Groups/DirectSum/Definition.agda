{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations

module Groups.DirectSum.Definition where

directSum : {m n o p : _} → {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (h : Group T _·B_) → Group (directSumSetoid S T) (λ x1 y1 → (((_&&_.fst x1) ·A (_&&_.fst y1)) ,, ((_&&_.snd x1) ·B (_&&_.snd y1))))
Group.+WellDefined (directSum {A = A} {B} g h) (s ,, t) (u ,, v) = Group.+WellDefined g s u ,, Group.+WellDefined h t v
Group.0G (directSum {A = A} {B} g h) = (Group.0G g ,, Group.0G h)
Group.inverse (directSum {A = A} {B} g h) (g1 ,, h1) = (Group.inverse g g1) ,, (Group.inverse h h1)
Group.+Associative (directSum {A = A} {B} g h) = Group.+Associative g ,, Group.+Associative h
Group.identRight (directSum {A = A} {B} g h) = Group.identRight g ,, Group.identRight h
Group.identLeft (directSum {A = A} {B} g h) = Group.identLeft g ,, Group.identLeft h
Group.invLeft (directSum {A = A} {B} g h) = Group.invLeft g ,, Group.invLeft h
Group.invRight (directSum {A = A} {B} g h) = Group.invRight g ,, Group.invRight h
