{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Setoids.Subset
open import Setoids.Functions.Definition
open import Sets.EquivalenceRelations

module Setoids.Functions.Lemmas {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f : A → B} (w : WellDefined S T f) where

inverseImagePred : {e : _} → {pred : B → Set e} → (sub : subset T pred) → A → Set (b ⊔ d ⊔ e)
inverseImagePred {pred = pred} subset a = Sg B (λ b → (pred b) && (Setoid._∼_ T (f a) b))

inverseImageWellDefined : {e : _} {pred : B → Set e} → (sub : subset T pred) → subset S (inverseImagePred sub)
inverseImageWellDefined sub {x} {y} x=y (b , (predB ,, fx=b)) = f x , (sub (symmetric fx=b) predB ,, symmetric (w x=y))
  where
    open Setoid T
    open Equivalence eq
