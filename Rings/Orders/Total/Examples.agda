{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Orders.Total.Definition
open import Setoids.Setoids
open import Functions.Definition
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Modulo.Definition
open import Semirings.Definition
open import Orders.Total.Definition
open import Sequences
open import Numbers.Integers.Definition
open import Numbers.Integers.Addition
open import Numbers.Integers.Multiplication
open import Numbers.Integers.Order
open import Numbers.Rationals.Definition
open import Vectors
open import Fields.Fields

module Rings.Orders.Total.Examples where

open import Rings.Orders.Total.BaseExpansion (ℚOrdered) {10} (le 8 refl)
open Field ℚField

t : Vec ℚ 5
t = take 5 (partialSums (funcToSequence injectionNQ))

u : Vec ℚ 5
u = vecMap injectionNQ (0 ,- (1 ,- (3 ,- (6 ,- (10 ,- [])))))

pr : Vec (ℚ && ℚ) 5
pr = vecZip t u

ans : vecAllTrue (λ x → _&&_.fst x =Q _&&_.snd x) pr
ans = refl ,, (refl ,, (refl ,, (refl ,, (refl ,, record {}))))

open import Rings.InitialRing ℚRing

a : Sequence ℚ
a with allInvertible (fromN 10) (λ ())
... | 1/10 , pr1/10 = approximations 1/10 pr1/10 (baseNExpansion (underlying (allInvertible (injectionNQ 7) λ ())) (lessInherits (succIsPositive 0)) (lessInherits (le 5 refl)))

expected : Vec ℚ _
expected = record { num = nonneg 1 ; denom = nonneg 10 ; denomNonzero = f } ,- record { num = nonneg 14 ; denom = nonneg 100 ; denomNonzero = λ () } ,- record { num = nonneg 142 ; denom = nonneg 1000 ; denomNonzero = λ () } ,- []
  where
    f : nonneg 10 ≡ nonneg 0 → False
    f ()

ans' : vecAllTrue (λ x → _&&_.fst x =Q _&&_.snd x) (vecZip (take _ a) expected)
ans' = refl ,, (refl ,, (refl ,, record {}))
