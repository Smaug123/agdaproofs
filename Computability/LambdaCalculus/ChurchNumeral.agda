{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Decidable.Sets
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Semiring

module Computability.LambdaCalculus.ChurchNumeral where

open import UnorderedSet.Definition ℕDecideEquality
open import Computability.LambdaCalculus.Definition

private
  iter : ℕ → Term
  iter zero = var 0
  iter (succ n) = apply (var 1) (iter n)

church : ℕ → Term
church n = lam 1 (lam 0 (iter n))

churchSucc : Term
churchSucc = lam 0 (lam 1 (lam 2 (apply (var 1) (apply (apply (var 0) (var 1)) (var 2)))))
