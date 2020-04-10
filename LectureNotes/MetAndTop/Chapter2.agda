{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

open import Setoids.Setoids
open import Setoids.Subset
open import Setoids.Functions.Definition
open import LogicalFormulae
open import Functions
open import Lists.Lists
open import Setoids.Orders
open import Rings.Orders.Partial.Definition
open import Rings.Definition

module LectureNotes.MetAndTop.Chapter2 {a b c : _} {R : Set a} {S : Setoid {a} {b} R} {_<_ : Rel {a} {c} R} {_+_ _*_ : R → R → R} {ring : Ring S _+_ _*_} {ps : SetoidPartialOrder S _<_} (pRing : PartiallyOrderedRing ring ps) where

open Setoid S renaming (_∼_ to _∼R_)
open Ring ring

record Metric {d1 e : _} {A : Set d1} {T : Setoid {d1} {e} A} (d : A → A → R) : Set (a ⊔ b ⊔ c ⊔ d1 ⊔ e) where
  open Setoid T
  field
    dWellDefined : (x y v w : A) → x ∼ y → v ∼ w → (d x v) ∼R (d w y)
    dZero : (x y : A) → (d x y) ∼R 0R → x ∼ y
    dZero' : (x y : A) → x ∼ y → (d x y) ∼R 0R
    dSymmetric : (x y : A) → (d x y) ∼R (d y x)
    dTriangle : (x y z : A) → ((d x z) < ((d x y) + (d y z))) || ((d x z) ∼R ((d x y) + (d y z)))
  dNonnegative : (x y : A) → (0R < d x y) || (0R ∼R (d x y))
  dNonnegative x y = {!!}
