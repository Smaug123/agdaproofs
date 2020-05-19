{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
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
open import Numbers.Modulo.Definition
open import Orders.Total.Definition

module Fields.CauchyCompletion.BaseExpansion {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Ring R
open Group additiveGroup
open Field F
open import Fields.Orders.Limits.Definition {F = F} (record { oRing = order })
open import Fields.Orders.Total.Lemmas {F = F} (record { oRing = order })
open import Fields.Orders.Limits.Lemmas {F = F} (record { oRing = order })

open import Fields.Lemmas F
open import Fields.Orders.Lemmas {F = F} record { oRing = order }
open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.AbsoluteValue order
open import Rings.Orders.Partial.Lemmas pRing
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Setoid order F
open import Fields.CauchyCompletion.Addition order F
open import Fields.CauchyCompletion.Comparison order F
open import Fields.CauchyCompletion.Approximation order F
open import Rings.InitialRing R
open import Rings.Orders.Partial.Bounded pRing
open import Rings.Orders.Total.Bounded order
open import Rings.Orders.Total.Cauchy order

-- TODO this is not necessarily true :( the bounded sequence could oscillate between 1 and -1
cauchyTimesBoundedIsCauchy : {s : Sequence A} → cauchy s → {t : Sequence A} → Bounded t → cauchy (apply _*_ s t)
cauchyTimesBoundedIsCauchy {s} cau {t} (K , bounded) e 0<e with allInvertible K (boundNonzero (K , bounded))
... | 1/K , prK with cau (1/K * e) (orderRespectsMultiplication (reciprocalPositive K 1/K (boundGreaterThanZero (K , bounded)) (transitive *Commutative prK)) 0<e)
... | N , cauPr = N , ans
  where
    ans : {m n : ℕ} (N<m : N <N m) (N<n : N <N n) → (abs (index (apply _*_ s t) m + inverse (index (apply _*_ s t) n))) < e
    ans N<m N<n with cauPr N<m N<n
    ... | r = {!!}

boundedTimesCauchyIsCauchy : {s : Sequence A} → cauchy s → {t : Sequence A} → Bounded t → cauchy (apply _*_ t s)
boundedTimesCauchyIsCauchy {s} cau {t} bou = cauchyWellDefined (ans s t) (cauchyTimesBoundedIsCauchy cau bou)
  where
    ans : (s t : Sequence A) (m : ℕ) → index (apply _*_ s t) m ∼ index (apply _*_ t s) m
    ans s t m rewrite indexAndApply t s _*_ {m} | indexAndApply s t _*_ {m} = *Commutative

private
  digitExpansionSeq : {n : ℕ} → .(0<n : 0 <N n) → Sequence (ℤn n 0<n) → Sequence A
  Sequence.head (digitExpansionSeq {n} 0<n seq) = fromN (ℤn.x (Sequence.head seq))
  Sequence.tail (digitExpansionSeq {n} 0<n seq) = digitExpansionSeq 0<n (Sequence.tail seq)

  powerSeq : (i : A) → (start : A) → Sequence A
  Sequence.head (powerSeq i start) = start
  Sequence.tail (powerSeq i start) = powerSeq i (start * i)

  powerSeqInduction : (i : A) (start : A) → (m : ℕ) → (index (powerSeq i start) (succ m)) ∼ i * (index (powerSeq i start) m)
  powerSeqInduction i start zero = *Commutative
  powerSeqInduction i start (succ m) = powerSeqInduction i (start * i) m

  ofBaseExpansionSeq : {n : ℕ} → .(0<n : 0 <N n) → Sequence (ℤn n 0<n) → Sequence A
  ofBaseExpansionSeq {succ n} 0<n seq = apply _*_ (digitExpansionSeq 0<n seq) (powerSeq pow pow)
    where
      pow : A
      pow = underlying (allInvertible (fromN (succ n)) (charNotN n))

  powerSeqPositive : {i : A} → (0R < i) → {s : A} → (0R < s) → (m : ℕ) → 0R < index (powerSeq i s) m
  powerSeqPositive {i} 0<i {s} 0<s zero = 0<s
  powerSeqPositive {i} 0<i {s} 0<s (succ m) = <WellDefined reflexive (symmetric (powerSeqInduction i s m)) (orderRespectsMultiplication 0<i (powerSeqPositive 0<i 0<s m))

  powerSeqConvergesTo0 : (i : A) → (0R < i) → (i < 1R) → {s : A} → (0R < s) → (powerSeq i s) ~> 0G
  powerSeqConvergesTo0 i 0<i i<1 {s} 0<s e 0<e = {!!}

  powerSeqConverges : (i : A) → (0R < i) → (i < 1R) → {s : A} → (0R < s) → cauchy (powerSeq i s)
  powerSeqConverges i 0<i i<1 {s} 0<s = convergentSequenceCauchy nontrivial {r = 0R} (powerSeqConvergesTo0 i 0<i i<1 0<s)

  0<n : {n : ℕ} → 1 <N n → 0 <N n
  0<n 1<n = TotalOrder.<Transitive ℕTotalOrder (le 0 refl) 1<n

  digitExpansionBoundedLemma : {n : ℕ} → .(0<n : 0 <N n) → (seq : Sequence (ℤn n 0<n)) → (m : ℕ) → index (digitExpansionSeq _ seq) m < fromN n
  digitExpansionBoundedLemma {n} 0<n seq zero with Sequence.head seq
  ... | record { x = x ; xLess = xLess } = fromNPreservesOrder (0<1 nontrivial) {x} {n} ((squash<N xLess))
  digitExpansionBoundedLemma 0<n seq (succ m) = digitExpansionBoundedLemma 0<n (Sequence.tail seq) m

  digitExpansionBoundedLemma2 : {n : ℕ} → .(0<n : 0 <N n) → (seq : Sequence (ℤn n 0<n)) → (m : ℕ) → inverse (fromN n) < index (digitExpansionSeq 0<n seq) m
  digitExpansionBoundedLemma2 {n} 0<n seq zero = <WellDefined identLeft (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) (orderRespectsAddition {_} {fromN (ℤn.x (Sequence.head seq)) + fromN n} (<WellDefined reflexive (fromNPreserves+ (ℤn.x (Sequence.head seq)) n) (fromNPreservesOrder (0<1 nontrivial) {0} {ℤn.x (Sequence.head seq) +N n} (canAddToOneSideOfInequality' _ (squash<N 0<n)))) (inverse (fromN n)))
  digitExpansionBoundedLemma2 0<n seq (succ m) = digitExpansionBoundedLemma2 0<n (Sequence.tail seq) m

  digitExpansionBounded : {n : ℕ} → .(0<n : 0 <N n) → (seq : Sequence (ℤn n 0<n)) → Bounded (digitExpansionSeq 0<n seq)
  digitExpansionBounded {n} 0<n seq = fromN n , λ m → ((digitExpansionBoundedLemma2 0<n seq m) ,, digitExpansionBoundedLemma 0<n seq m)

private
  1/nPositive : (n : ℕ) → 0R < underlying (allInvertible (fromN (succ n)) (charNotN n))
  1/nPositive n with allInvertible (fromN (succ n)) (charNotN n)
  ... | a , b = reciprocalPositive (fromN (succ n)) a (fromNPreservesOrder (0<1 nontrivial) (succIsPositive n)) (transitive *Commutative b)

  1/n<1 : (n : ℕ) → (0 <N n) → underlying (allInvertible (fromN (succ n)) (charNotN n)) < 1R
  1/n<1 n 1<n with allInvertible (fromN (succ n)) (charNotN n)
  ... | a , b = reciprocal<1 (fromN (succ n)) a (<WellDefined identRight reflexive (fromNPreservesOrder (0<1 nontrivial) {1} {succ n} (succPreservesInequality 1<n))) (transitive *Commutative b)

-- Construct the real that is the given base-n expansion between 0 and 1.
ofBaseExpansion : {n : ℕ} → .(1<n : 1 <N n) → (fromN n ∼ 0R → False) → Sequence (ℤn n (0<n 1<n)) → CauchyCompletion
ofBaseExpansion {succ n} 1<n charNotN seq = record { elts = ofBaseExpansionSeq (0<n 1<n) seq ; converges = boundedTimesCauchyIsCauchy (powerSeqConverges _ (1/nPositive n) (1/n<1 n (canRemoveSuccFrom<N (squash<N 1<n))) (1/nPositive n)) (digitExpansionBounded (0<n 1<n) seq)}

toBaseExpansion : {n : ℕ} → .(1<n : 1 <N n) → (fromN n ∼ 0R → False) → (a : CauchyCompletion) → 0R r<C a → a <Cr 1R → Sequence (ℤn n (0<n 1<n))
Sequence.head (toBaseExpansion {n} 1<n charNotN c 0<c c<1) = {!!}
 -- TOOD: approximate c to within 1/n^2, extract the first decimal of the result.
Sequence.tail (toBaseExpansion {n} 1<n charNotN c 0<c c<1) = toBaseExpansion 1<n charNotN {!!} {!!} {!!}

baseExpansionProof : {n : ℕ} → .{1<n : 1 <N n} → {charNotN : fromN n ∼ 0R → False} → (as : CauchyCompletion) → (0<a : 0R r<C as) → (a<1 : as <Cr 1R) → Setoid._∼_ cauchyCompletionSetoid (ofBaseExpansion 1<n charNotN (toBaseExpansion 1<n charNotN as 0<a a<1)) as
baseExpansionProof = {!!}
