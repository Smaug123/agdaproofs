{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Abelian.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.EuclideanAlgorithm
open import Numbers.Primes.PrimeNumbers

module Rings.Characteristic {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.InitialRing R
open Ring R
open Setoid S
open Equivalence eq
open Group additiveGroup

characteristicWellDefined : (0R ∼ 1R → False) → {n m : ℕ} → Prime n → Prime m → fromN n ∼ 0R → fromN m ∼ 0R → n ≡ m
characteristicWellDefined 0!=1 {n} {m} pN pM n=0 m=0 with divisionDecidable m n
... | inl n|m = equalityCommutative (primeDivPrimeImpliesEqual pM pN n|m)
... | inr notDiv with hcfPrimeIsOne {m} {n} pM notDiv
... | bl = exFalso (0!=1 v)
  where
    t : (n *N extendedHcf.extended1 (euclid n m) ≡ m *N extendedHcf.extended2 (euclid n m) +N extendedHcf.c (euclid n m)) || (n *N extendedHcf.extended1 (euclid n m) +N extendedHcf.c (euclid n m) ≡ m *N extendedHcf.extended2 (euclid n m))
    t = extendedHcf.extendedProof (euclid n m)
    u : (n *N extendedHcf.extended1 (euclid n m) ≡ m *N extendedHcf.extended2 (euclid n m) +N 1) || (n *N extendedHcf.extended1 (euclid n m) +N 1 ≡ m *N extendedHcf.extended2 (euclid n m))
    u with t
    ... | inl x = inl (transitivity x (applyEquality (λ i → m *N extendedHcf.extended2 (euclid n m) +N i) bl))
    ... | inr x = inr (transitivity (applyEquality (n *N extendedHcf.extended1 (euclid n m) +N_) (equalityCommutative bl)) x)
    v : 0R ∼ 1R
    v with u
    ... | inr x = symmetric (transitive (symmetric (transitive (fromNPreserves+ (n *N extendedHcf.extended1 (euclid n m)) 1) (transitive (+WellDefined (transitive (fromNPreserves* n (extendedHcf.extended1 (euclid n m))) (transitive (*WellDefined n=0 reflexive) timesZero')) identRight) identLeft))) (transitive (fromNWellDefined x) (transitive (fromNPreserves* m (extendedHcf.extended2 (euclid n m))) (transitive (*WellDefined m=0 reflexive) timesZero'))))
    ... | inl x = transitive (transitive (transitive (symmetric timesZero') (transitive (*WellDefined (symmetric n=0) reflexive) (transitive (symmetric (fromNPreserves* n (extendedHcf.extended1 (euclid n m)))) (transitive (fromNWellDefined x) (transitive (fromNPreserves+ (m *N extendedHcf.extended2 (euclid n m)) 1) (+WellDefined (fromNPreserves* m (extendedHcf.extended2 (euclid n m))) reflexive)))))) (+WellDefined (transitive (*WellDefined m=0 reflexive) timesZero') (identRight))) identLeft
