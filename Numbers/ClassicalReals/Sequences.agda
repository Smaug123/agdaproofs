
{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Numbers.ClassicalReals.RealField
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Sets.EquivalenceRelations
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Fields
open import Groups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Sequences

module Numbers.ClassicalReals.Sequences (ℝ : RealField) where

open RealField ℝ
open Setoid S
open Equivalence eq
open Ring R
open Field F
open SetoidPartialOrder pOrder
open import Fields.Orders.LeastUpperBounds.Definition pOrder
open import Rings.Orders.Total.Lemmas orderedRing
open import Rings.Orders.Partial.Lemmas pOrderedRing
open Group additiveGroup
open PartiallyOrderedRing pOrderedRing
open SetoidTotalOrder (TotallyOrderedRing.total orderedRing)
open import Rings.InitialRing R
open import Fields.Orders.Lemmas oField
open import Rings.Lemmas R
open import Groups.Lemmas additiveGroup
open import Numbers.Intervals.Definition pOrderedRing
open import Numbers.Intervals.Arithmetic pOrderedRing
open import Fields.Lemmas F
open import Fields.Orders.Total.Definition F

orderedField : TotallyOrderedField pOrderedRing
orderedField = record { oRing = orderedRing }

open import Fields.Orders.Limits.Definition orderedField

StrictlyIncreasing : Sequence A → Set c
StrictlyIncreasing x = (n : ℕ) → (index x n) < (index x (succ n))

Increasing : Sequence A → Set (b ⊔ c)
Increasing x = (n : ℕ) → ((index x n) < (index x (succ n))) || ((index x n) ∼ (index x (succ n)))

Bounded : Sequence A → Set (a ⊔ c)
Bounded x = Sg A (λ K → (n : ℕ) → index x n < K)

sequencePredicate : (x : Sequence A) → A → Set b
sequencePredicate x a = Sg ℕ (λ n → index x n ∼ a)

sequenceSubset : (x : Sequence A) → subset S (sequencePredicate x)
sequenceSubset sequence {x} {y} x=y (n , sn=x) = n , transitive sn=x x=y

boundedSequenceBounds : (K : A) (x : Sequence A) → ((n : ℕ) → index x n < K) → UpperBound (sequenceSubset x) K
boundedSequenceBounds K x pr y (n , y=xn) = inl (<WellDefined y=xn reflexive (pr n))

increasingBoundedLimit : (x : Sequence A) → Increasing x → Bounded x → A
increasingBoundedLimit x increasing (K , kIsBound) with lub (sequenceSubset x) ((index x 0) , (0 , reflexive)) (K , boundedSequenceBounds K x kIsBound)
... | a , _ = a

increasingBoundedConverges : (x : Sequence A) → (increasing : Increasing x) → (bounded : Bounded x) → x ~> (increasingBoundedLimit x increasing bounded)
increasingBoundedConverges x increasing (K , prBound) with lub (sequenceSubset x) (Sequence.head x , (0 , reflexive)) (K , boundedSequenceBounds K x prBound)
... | lub , isLub = {!!}
