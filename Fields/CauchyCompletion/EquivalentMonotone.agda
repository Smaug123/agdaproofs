{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Definition
open import Groups.Definition
open import Groups.Groups
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals

module Fields.CauchyCompletion.EquivalentMonotone {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder {_<_ = _<_} pOrder} {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Field F
open Group (Ring.additiveGroup R)
open Ring R

open import Fields.Lemmas F
open import Fields.Orders.Lemmas {F = F} record { oRing = order }
open import Rings.Orders.Lemmas(order)
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Multiplication order F charNot2
open import Fields.CauchyCompletion.Addition order F charNot2
open import Fields.CauchyCompletion.Setoid order F charNot2
open import Fields.CauchyCompletion.Group order F charNot2
open import Fields.CauchyCompletion.Ring order F charNot2
open import Fields.CauchyCompletion.Comparison order F charNot2
open import Fields.CauchyCompletion.Approximation order F charNot2

halvingSequence : (start : A) → Sequence A
Sequence.head (halvingSequence start) = start
Sequence.tail (halvingSequence start) with halve charNot2 start
Sequence.tail (halvingSequence start) | start/2 , _ = halvingSequence start/2

halvingSequenceMultiple : (start : A) → {n : ℕ} → index (halvingSequence start) n ∼ index (map (start *_) (halvingSequence (Ring.1R R))) n
halvingSequenceMultiple start {zero} = Equivalence.symmetric eq (Equivalence.transitive eq *Commutative identIsIdent)
halvingSequenceMultiple start {succ n} with halve charNot2 start
... | start/2 , _ with allInvertible (1R + 1R) charNot2
halvingSequenceMultiple start {succ n} | start/2 , b | 1/2 , pr1/2 rewrite equalityCommutative (mapAndIndex (halvingSequence (1R * 1/2)) (_*_ start) n) = Equivalence.transitive eq (halvingSequenceMultiple start/2 {n}) f
  where
    g : (start * (1/2 * index (halvingSequence 1R) n)) ∼ (start * index (map (_*_ (1R * 1/2)) (halvingSequence 1R)) n)
    g rewrite equalityCommutative (mapAndIndex (halvingSequence 1R) (_*_ (1R * 1/2)) n) = *WellDefined (Equivalence.reflexive eq) (*WellDefined (Equivalence.symmetric eq identIsIdent) (Equivalence.reflexive eq))
    f : index (map (_*_ start/2) (halvingSequence 1R)) n ∼ (start * index (halvingSequence (1R * 1/2)) n)
    f rewrite equalityCommutative (mapAndIndex (halvingSequence 1R) (_*_ start/2) n) = Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq b) (Equivalence.reflexive eq)) (halfHalves 1/2 (Equivalence.transitive eq (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative identIsIdent)) (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative identIsIdent))) (Equivalence.symmetric eq *DistributesOver+)) pr1/2)))) (Equivalence.reflexive eq)) (Equivalence.symmetric eq *Associative)) g) (Equivalence.symmetric eq (*WellDefined (Equivalence.reflexive eq) (halvingSequenceMultiple (1R * 1/2) {n})))

Decreasing : Sequence A → Set o
Decreasing seq = ∀ (N : ℕ) → (index seq (succ N)) < (index seq N)

halvingSequencePositive : (n : ℕ) → 0G < index (halvingSequence 1R) n
halvingSequencePositive zero = 0<1 (charNot2ImpliesNontrivial charNot2)
halvingSequencePositive (succ n) with halve charNot2 1R
halvingSequencePositive (succ n) | 1/2 , pr1/2 = <WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (Equivalence.transitive eq (halvingSequenceMultiple 1/2 {n}) (Equivalence.transitive eq (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (mapAndIndex (halvingSequence 1R) (_*_ 1/2) n)) *Commutative))) (orderRespectsMultiplication (halvingSequencePositive n) (halvePositive 1/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr1/2) (0<1 (charNot2ImpliesNontrivial charNot2)))))

decreasingHalving : Decreasing (halvingSequence 1R)
decreasingHalving N with halve charNot2 1R
decreasingHalving N | 1/2 , pr1/2 with (halfLess 1/2 1R (0<1 (charNot2ImpliesNontrivial charNot2)) pr1/2)
... | 1/2<1 = <WellDefined (Equivalence.transitive eq (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (equalityCommutative (mapAndIndex (halvingSequence 1R) (_*_ 1/2) N))) (Equivalence.symmetric eq (halvingSequenceMultiple 1/2 {N}))) identIsIdent (ringCanMultiplyByPositive {c = index (halvingSequence 1R) N} (halvingSequencePositive N) 1/2<1)

halvesCauchy : cauchy (halvingSequence 1R)
halvesCauchy e 0<e = {!!}

multipleOfCauchyIsCauchy : (mult : A) → (seq : Sequence A) → cauchy seq → cauchy (map (mult *_) seq)
multipleOfCauchyIsCauchy mult seq seqCauchy e 0<e with SetoidTotalOrder.totality tOrder 0R mult
multipleOfCauchyIsCauchy mult seq seqCauchy e 0<e | inl (inl x) with allInvertible mult λ pr → irreflexive (<WellDefined (Equivalence.reflexive eq) pr x)
... | 1/mult , pr1/mult = {!!}
multipleOfCauchyIsCauchy mult seq seqCauchy e 0<e | inl (inr x) with allInvertible mult λ pr → irreflexive (<WellDefined pr (Equivalence.reflexive eq) x)
... | 1/mult , pr1/mult = {!!}
multipleOfCauchyIsCauchy mult seq seqCauchy e 0<e | inr 0=mult = 0 , ans
  where
    ans : {m n : ℕ} → (0 <N m) → (0 <N n) → abs (index (map (_*_ mult) seq) m + inverse (index (map (_*_ mult) seq) n)) < e
    ans {m} {n} _ _ rewrite equalityCommutative (mapAndIndex seq (_*_ mult) m) | equalityCommutative (mapAndIndex seq (_*_ mult) n) = <WellDefined {!!} (Equivalence.reflexive eq) 0<e

halvingSequenceCauchy : (start : A) → cauchy (halvingSequence start)
halvingSequenceCauchy start = {!!}

sequenceAllAbove : (a : CauchyCompletion) → Sequence A
sequenceAllAbove a = go (Ring.1R R) (0<1 (charNot2ImpliesNontrivial charNot2))
  where
    go : (e : A) → (0G < e) → Sequence A
    Sequence.head (go e 0<e) = rationalApproximatelyAbove a e 0<e
    Sequence.tail (go e 0<e) with halve charNot2 e
    ... | e/2 , prE/2 = go e/2 (halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e))

sequenceAllAboveCauchy : (a : CauchyCompletion) → cauchy (sequenceAllAbove a)
sequenceAllAboveCauchy a e 0<e = {!!}
  -- find N such that 1/2^N < e
  -- show that this N is enough

-- show that sequenceAllAbove ∼ a
-- monotonify sequenceAllAbove
-- show that monotonify of a sequence which is all above its limit still converges to that limit
