{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions.Definition
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Semirings.Definition

module Fields.CauchyCompletion.NearlyTotalOrder {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Ring R
open Group additiveGroup
open Field F
open import Fields.Orders.Lemmas {F = F} {pRing} (record { oRing = order })
open import Setoids.Orders.Partial.Sequences pOrder

open import Rings.InitialRing R
open import Rings.Orders.Partial.Lemmas pRing
open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.Cauchy order
open import Rings.Orders.Total.AbsoluteValue order
open import Fields.Lemmas F
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Setoid order F
open import Fields.CauchyCompletion.Group order F
open import Fields.CauchyCompletion.Addition order F
open import Fields.CauchyCompletion.Approximation order F
open import Fields.CauchyCompletion.Comparison order F
open import Fields.CauchyCompletion.PartiallyOrderedRing order F
open import Fields.Orders.Total.Lemmas {F = F} (record { oRing = order })

makeIncreasingLemma : (a : A) (s : Sequence A) → Sequence A
Sequence.head (makeIncreasingLemma a s) with totality a (Sequence.head s)
... | inl (inl x) = Sequence.head s
... | inl (inr x) = a
... | inr x = a
Sequence.tail (makeIncreasingLemma a s) = makeIncreasingLemma (Sequence.head (makeIncreasingLemma a s)) (Sequence.tail s)

makeIncreasingLemmaIsIncreasing : (a : A) (s : Sequence A) → WeaklyIncreasing (makeIncreasingLemma a s)
makeIncreasingLemmaIsIncreasing a s zero with totality a (Sequence.head s)
makeIncreasingLemmaIsIncreasing a s zero | inl (inl x) with totality (Sequence.head s) (Sequence.head (Sequence.tail s))
makeIncreasingLemmaIsIncreasing a s zero | inl (inl x) | inl (inl y) = inl y
makeIncreasingLemmaIsIncreasing a s zero | inl (inl x) | inl (inr y) = inr reflexive
makeIncreasingLemmaIsIncreasing a s zero | inl (inl x) | inr y = inr reflexive
makeIncreasingLemmaIsIncreasing a s zero | inl (inr x) with totality a (Sequence.head (Sequence.tail s))
... | inl (inl y) = inl y
... | inl (inr y) = inr reflexive
... | inr y = inr reflexive
makeIncreasingLemmaIsIncreasing a s zero | inr x with totality a (Sequence.head (Sequence.tail s))
... | inl (inl y) = inl y
... | inl (inr y) = inr reflexive
... | inr y = inr reflexive
makeIncreasingLemmaIsIncreasing a s (succ m) = makeIncreasingLemmaIsIncreasing (Sequence.head (makeIncreasingLemma a s)) (Sequence.tail s) m

makeIncreasing : Sequence A → Sequence A
Sequence.head (makeIncreasing x) = Sequence.head x
Sequence.tail (makeIncreasing x) = makeIncreasingLemma (Sequence.head x) (Sequence.tail x)

makeIncreasingIsIncreasing : (a : Sequence A) → WeaklyIncreasing (makeIncreasing a)
makeIncreasingIsIncreasing a zero with totality (Sequence.head a) (Sequence.head (Sequence.tail a))
... | inl (inl x) = inl x
... | inl (inr x) = inr reflexive
... | inr x = inr reflexive
makeIncreasingIsIncreasing a (succ m) = makeIncreasingLemmaIsIncreasing _ _ m

approximateIncreasingSeqRaw : CauchyCompletion → Sequence A
approximateIncreasingSeqRaw a = funcToSequence f
  where
    f : ℕ → A
    f n with allInvertible (fromN (succ n)) λ n=0 → irreflexive (<WellDefined reflexive n=0 (fromNPreservesOrder (0<1 nontrivial) (succIsPositive n)))
    ... | 1/n , prN = underlying (approximateBelow a 1/n (reciprocalPositive' (fromN (succ n)) 1/n (fromNPreservesOrder (0<1 nontrivial) (succIsPositive n)) prN))

approximateIncreasingSeq : CauchyCompletion → Sequence A
approximateIncreasingSeq a = makeIncreasing (approximateIncreasingSeqRaw a)

approximateIncreasingConverges : (a : CauchyCompletion) → cauchy (approximateIncreasingSeq a)
approximateIncreasingConverges a e 0<e = {!!}

approximateIncreasingIncreases : (a : CauchyCompletion) → WeaklyIncreasing (approximateIncreasingSeq a)
approximateIncreasingIncreases a = makeIncreasingIsIncreasing (approximateIncreasingSeqRaw a)

approximateIncreasing : CauchyCompletion → CauchyCompletion
approximateIncreasing a = record { elts = approximateIncreasingSeq a ; converges = approximateIncreasingConverges a }

approximateIncreasingEqual : (a : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid (approximateIncreasing a) a
approximateIncreasingEqual a e 0<e = {!!}

decideSign : (a : CauchyCompletion) → (Setoid._∼_ cauchyCompletionSetoid a (injection 0R) → False) → (a <Cr 0R) || (0R r<C a)
decideSign a a!=0 = {!!}
  where

private
  lemma : (a b : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid ((b +C (-C a)) +C a) b
  lemma a b = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges ((b +C (-C a)) +C a) }} {record { converges = CauchyCompletion.converges (b +C ((-C a) +C a)) }} {record { converges = CauchyCompletion.converges b }} (Group.+Associative' CGroup {record { converges = CauchyCompletion.converges b }} {record { converges = CauchyCompletion.converges (-C a) }} { record { converges = CauchyCompletion.converges a }}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record {converges = CauchyCompletion.converges (b +C ((-C a) +C a))}} {record { converges = CauchyCompletion.converges (b +C (injection 0R))}} {record {converges = CauchyCompletion.converges b}} (Group.+WellDefinedRight CGroup {record {converges = CauchyCompletion.converges b}} {record {converges = CauchyCompletion.converges ((-C a) +C a)}} {record { converges = CauchyCompletion.converges (injection 0R)}} (Group.invLeft CGroup {record { converges = CauchyCompletion.converges a }})) (Group.identRight CGroup {record { converges = CauchyCompletion.converges b }}))

nearlyTotal : (a b : CauchyCompletion) → (Setoid._∼_ cauchyCompletionSetoid a b → False) → (a <C b) || (b <C a)
nearlyTotal a b a!=b with decideSign (b +C (-C a)) λ bad → a!=b (Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges b }} {record { converges = CauchyCompletion.converges a  }} (transferToRight CGroup {record { converges = CauchyCompletion.converges b }} {record { converges = CauchyCompletion.converges a }} bad))
... | inl x = inr (<CWellDefined (lemma a b) (Group.identLeft CGroup {record { converges = CauchyCompletion.converges a }}) (PartiallyOrderedRing.orderRespectsAddition CpOrderedRing (<CRelaxR x) a))
... | inr x = inl (<CWellDefined (Group.identLeft CGroup {record { converges = CauchyCompletion.converges a }}) (lemma a b) (PartiallyOrderedRing.orderRespectsAddition CpOrderedRing (<CRelaxL x) a))
