{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

-- Following Part IB's course Groups, Rings, and Modules, we take rings to be commutative with one.
module Rings.Definition where

record Ring {n m} {A : Set n} (S : Setoid {n} {m} A) (_+_ : A → A → A) (_*_ : A → A → A) : Set (lsuc n ⊔ m) where
  field
    additiveGroup : Group S _+_
  open Group additiveGroup
  open Setoid S
  open Equivalence eq
  0R : A
  0R = 0G
  _-R_ : A → A → A
  a -R b = a + (inverse b)
  field
    *WellDefined : {r s t u : A} → (r ∼ t) → (s ∼ u) → r * s ∼ t * u
    1R : A
    groupIsAbelian : {a b : A} → a + b ∼ b + a
    *Associative : {a b c : A} → (a * (b * c)) ∼ (a * b) * c
    *Commutative : {a b : A} → a * b ∼ b * a
    *DistributesOver+ : {a b c : A} → a * (b + c) ∼ (a * b) + (a * c)
    identIsIdent : {a : A} → 1R * a ∼ a
  timesZero : {a : A} → a * 0R ∼ 0R
  timesZero {a} = symmetric (transitive (transitive (symmetric invLeft) (+WellDefined reflexive (transitive (*WellDefined {a} {a} reflexive (symmetric identRight)) *DistributesOver+))) (transitive +Associative (transitive (+WellDefined invLeft reflexive) identLeft)))
  timesZero' : {a : A} → 0R * a ∼ 0R
  timesZero' {a} = transitive *Commutative timesZero
  *DistributesOver+' : {a b c : A} → (a + b) * c ∼ (a * c) + (b * c)
  *DistributesOver+' = transitive *Commutative (transitive *DistributesOver+ (+WellDefined *Commutative *Commutative))
  *Associative' : {a b c : A} → ((a * b) * c) ∼ (a * (b * c))
  *Associative' = symmetric *Associative
  identIsIdent' : {a : A} → a * 1R ∼ a
  identIsIdent' = transitive *Commutative identIsIdent
