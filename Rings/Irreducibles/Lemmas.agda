{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.IntegralDomains.Definition
open import Rings.Definition


module Rings.Irreducibles.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Irreducibles.Definition intDom
open import Rings.Divisible.Definition R
open import Rings.Units.Definition R

open Setoid S
open Equivalence eq
open Ring R

dividesIrreducibleImpliesUnit : {r c : A} → Irreducible r → c ∣ r → (r ∣ c → False) → Unit c
dividesIrreducibleImpliesUnit {r} {c} irred (x , cx=r) notAssoc = Irreducible.irreducible irred x c (transitive *Commutative cx=r) nonunit
  where
    nonunit : Unit x → False
    nonunit (a , xa=1) = notAssoc (a , transitive (transitive (transitive (transitive (*WellDefined (symmetric cx=r) reflexive) (symmetric *Associative)) *Commutative) (*WellDefined xa=1 reflexive)) identIsIdent)
