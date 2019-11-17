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
open import Vectors
open import Lists.Lists
open import Maybe

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Polynomials.Addition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Groups.Polynomials.Definition G
open Setoid S
open Equivalence eq
open Group G

_+P_ : NaivePoly → NaivePoly → NaivePoly
_+P_ = listZip _+_ id id

PidentRight : {m : NaivePoly} → polysEqual (m +P []) m
PidentRight {[]} = record {}
PidentRight {x :: m} = reflexive ,, identityOfIndiscernablesLeft polysEqual (Equivalence.reflexive (Setoid.eq naivePolySetoid)) (equalityCommutative (mapId m))

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
+PwellDefined {[]} {n :: ns} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (symmetric identLeft) (+WellDefined (symmetric fst) fst2) ,, (+PwellDefined snd snd2)
+PwellDefined {m :: ms} {[]} {[]} {[]} (fst ,, snd) _ = fst ,, identityOfIndiscernablesLeft polysEqual snd (equalityCommutative (mapId ms))
+PwellDefined {m :: ms} {[]} {[]} {x :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive fst (symmetric fst2) ,, ans
  where
    ans : polysEqual (map (λ z → z) ms) (map (λ z → z) ys)
    ans rewrite mapId ms | mapId ys = Equivalence.transitive (Setoid.eq naivePolySetoid) snd snd2
+PwellDefined {m :: ms} {[]} {x :: xs} {[]} (fst ,, snd) n=y = fst ,, ans
  where
    ans : polysEqual (map (λ z → z) ms) (map (λ z → z) xs)
    ans rewrite mapId ms | mapId xs = snd
+PwellDefined {m :: ms} {[]} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (symmetric identRight) (+WellDefined fst (symmetric fst2)) ,, identityOfIndiscernablesLeft polysEqual (Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.symmetric (Setoid.eq naivePolySetoid) PidentRight) (+PwellDefined snd snd2)) (equalityCommutative (mapId ms))
+PwellDefined {m :: ms} {n :: ns} {[]} {[]} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identLeft ,, +PwellDefined snd snd2
+PwellDefined {m :: ms} {n :: ns} {[]} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identLeft ,, +PwellDefined snd snd2
+PwellDefined {m :: ms} {n :: ns} {x :: xs} {[]} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identRight ,, identityOfIndiscernablesRight polysEqual (Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined snd snd2) PidentRight) (equalityCommutative (mapId xs))
+PwellDefined {m :: ms} {n :: ns} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = +WellDefined fst fst2 ,, +PwellDefined snd snd2

PidentLeft : {m : NaivePoly} → polysEqual ([] +P m) m
PidentLeft {[]} = record {}
PidentLeft {x :: m} = reflexive ,, identityOfIndiscernablesLeft polysEqual (Equivalence.reflexive (Setoid.eq naivePolySetoid)) (equalityCommutative (mapId m))
