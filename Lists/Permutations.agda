{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Functions
open import Lists.Definition
open import Lists.Fold.Fold
open import Lists.Concat
open import Lists.Length
open import Setoids.Setoids
open import Maybe
open import Numbers.Naturals.Semiring

module Lists.Permutations {a b : _} {A : Set a} (S : Setoid {a} {b} A) (decidable : (x y : A) → (Setoid._∼_ S x y) || ((Setoid._∼_ S x y) → False)) where

open Setoid S
open Equivalence eq

indexOf : (a : A) → (l : List A) → Maybe ℕ
indexOf a [] = no
indexOf a (x :: l) with decidable a x
... | inl eq = yes 0
... | inr noneq = mapMaybe succ (indexOf a l)

eltAt : (n : ℕ) → (l : List A) → Maybe A
eltAt n [] = no
eltAt zero (x :: l) = yes x
eltAt (succ n) (x :: l) = eltAt n l

indexOfIsIndexOf : (a : A) → (l : List A) → {n : ℕ} → indexOf a l ≡ yes n → Sg A (λ b → (eltAt n l ≡ yes b) && (b ∼ a))
indexOfIsIndexOf a (x :: l) {n} ind with decidable a x
indexOfIsIndexOf a (x :: l) {.0} refl | inl a=x = x , (refl ,, symmetric a=x)
indexOfIsIndexOf a (x :: l) {zero} ind | inr a!=x with indexOf a l
indexOfIsIndexOf a (x :: l) {zero} () | inr a!=x | no
indexOfIsIndexOf a (x :: l) {zero} () | inr a!=x | yes _
indexOfIsIndexOf a (x :: l) {succ n} ind | inr a!=x with mapMaybePreservesYes ind
... | m , (pr ,, z=n) = indexOfIsIndexOf a l (transitivity pr (applyEquality yes (succInjective z=n)))

Permutation : (List A) → (List A) → Set
Permutation [] [] = True
Permutation [] (x :: l2) = False
Permutation (x :: l1) [] = False
Permutation (a :: as) (b :: bs) with decidable a b
Permutation (a :: as) (b :: bs) | inl a=b = Permutation as bs
Permutation (a :: as) (b :: bs) | inr a!=b = {!!}
