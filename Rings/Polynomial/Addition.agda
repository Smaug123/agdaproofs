{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Vectors
open import Lists.Lists
open import Maybe
open import Rings.Homomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Polynomial.Addition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Rings.Polynomial.Definition R
open Setoid S
open Equivalence eq
open Ring R
open Group additiveGroup

_+P_ : NaivePoly → NaivePoly → NaivePoly
_+P_ = listZip _+_ id id

+PwellDefined : {m n x y : NaivePoly} → polysEqual m x → polysEqual n y → polysEqual (m +P n) (x +P y)
+PwellDefined {[]} {[]} {[]} {[]} m=x n=y = record {}
+PwellDefined {[]} {[]} {[]} {x :: y} m=x (fst ,, snd) = fst ,, identityOfIndiscernablesRight polysEqual snd (equalityCommutative (mapId y))
+PwellDefined {[]} {[]} {x :: xs} {[]} (fst ,, snd) n=y = fst ,, identityOfIndiscernablesRight polysEqual snd (equalityCommutative (mapId xs))
+PwellDefined {[]} {[]} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identRight ,, +PwellDefined {[]} {[]} {xs} {ys} snd snd2
+PwellDefined {[]} {n :: ns} {[]} {[]} m=x (fst ,, snd) = fst ,, identityOfIndiscernablesLeft polysEqual snd (equalityCommutative (mapId ns))
+PwellDefined {[]} {n :: ns} {[]} {y :: ys} m=x (fst ,, snd) = fst ,, +PwellDefined m=x snd
+PwellDefined {[]} {n :: ns} {x :: xs} {[]} (fst ,, snd) (fst2 ,, snd2) = transitive fst2 (symmetric fst) ,, ans
  where
    ans : polysEqual (map (λ z → z) ns) (map (λ z → z) xs)
    ans rewrite mapId ns | mapId xs = Equivalence.transitive (Setoid.eq naivePolySetoid) snd2 snd
+PwellDefined {[]} {n :: ns} {x :: xs} {y :: ys} m=x n=y = {!!}
+PwellDefined {m :: ms} {[]} {[]} {[]} m=x n=y = {!!}
+PwellDefined {m :: ms} {[]} {[]} {x :: ys} m=x n=y = {!!}
+PwellDefined {m :: ms} {[]} {x :: xs} {[]} m=x n=y = {!!}
+PwellDefined {m :: ms} {[]} {x :: xs} {y :: ys} m=x n=y = {!!}
+PwellDefined {m :: ms} {n :: ns} {[]} {[]} m=x n=y = {!!}
+PwellDefined {m :: ms} {n :: ns} {[]} {y :: ys} m=x n=y = {!!}
+PwellDefined {m :: ms} {n :: ns} {x :: xs} {[]} m=x n=y = {!!}
+PwellDefined {m :: ms} {n :: ns} {x :: xs} {y :: ys} m=x n=y = {!!}
