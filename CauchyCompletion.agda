{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Order
open import Groups.Definition
open import Groups.Groups
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals

module CauchyCompletion {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} (tOrder : SetoidTotalOrder {_<_ = _<_} pOrder) {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Ring R
open Group additiveGroup
open Field F

open import Rings.Orders.Lemmas(order)

cauchy : Sequence A → Set (m ⊔ o)
cauchy s = ∀ (ε : A) → (0R < ε) → Sg ℕ (λ N → ∀ {m n : ℕ} → (N <N m) → (N <N n) → abs ((index s m) -R (index s n)) < ε)

record CauchyCompletion : Set (m ⊔ o) where
  field
    elts : Sequence A
    converges : cauchy elts

injection : A → CauchyCompletion
CauchyCompletion.elts (injection a) = constSequence a
CauchyCompletion.converges (injection a) = λ ε 0<e → 0 , λ {m} {n} _ _ → <WellDefined (symmetric (identityOfIndiscernablesRight _∼_ (absWellDefined (index (constSequence a) m + inverse (index (constSequence a) n)) 0R (t m n)) (absZero order))) reflexive 0<e
  where
    t : (m n : ℕ) → index (constSequence a) m + inverse (index (constSequence a) n) ∼ 0R
    t m n = identityOfIndiscernablesLeft _∼_ (identityOfIndiscernablesLeft _∼_ invRight (equalityCommutative (applyEquality (λ i → a + inverse i) (indexAndConst a n)))) (applyEquality (_+ inverse (index (constSequence a) n)) (equalityCommutative (indexAndConst a m)))

halve : (a : A) → Sg A (λ i → i + i ∼ a)
-- TODO: we need to know the characteristic already
halve a with allInvertible (1R + 1R) charNot2
... | 1/2 , pr1/2 = (a * 1/2) , Equivalence.transitive eq (+WellDefined *Commutative *Commutative) (Equivalence.transitive eq (Equivalence.symmetric eq (*DistributesOver+ {1/2} {a} {a})) (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) r) (Equivalence.transitive eq (*Associative) (Equivalence.transitive eq (*WellDefined pr1/2 (Equivalence.reflexive eq)) identIsIdent))))
  where
    r : a + a ∼ (1R + 1R) * a
    r = Equivalence.symmetric eq (Equivalence.transitive eq *Commutative (Equivalence.transitive eq *DistributesOver+ (+WellDefined (Equivalence.transitive eq *Commutative identIsIdent) (Equivalence.transitive eq *Commutative identIsIdent))))

halvePositive : (a : A) → 0R < (a + a) → 0R < a
halvePositive a 0<2a with totality 0R a
halvePositive a 0<2a | inl (inl x) = x
halvePositive a 0<2a | inl (inr a<0) = exFalso (irreflexive {a + a} (SetoidPartialOrder.transitive pOrder (<WellDefined (Equivalence.reflexive eq) identRight (ringAddInequalities a<0 a<0)) 0<2a))
halvePositive a 0<2a | inr x = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq x) (Equivalence.symmetric eq x)) identRight) 0<2a))

lemm : (m : ℕ) (a b : Sequence A) → index (apply _+_ a b) m ≡ (index a m) + (index b m)
lemm zero a b = refl
lemm (succ m) a b = lemm m (Sequence.tail a) (Sequence.tail b)

_+C_ : CauchyCompletion → CauchyCompletion → CauchyCompletion
CauchyCompletion.elts (record { elts = a ; converges = convA } +C record { elts = b ; converges = convB }) = apply _+_ a b
CauchyCompletion.converges (record { elts = a ; converges = convA } +C record { elts = b ; converges = convB }) ε 0<e with halve ε
... | e/2 , e/2Pr with convA e/2 (halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq e/2Pr) 0<e))
CauchyCompletion.converges (record { elts = a ; converges = convA } +C record { elts = b ; converges = convB }) ε 0<e | e/2 , e/2Pr | Na , prA with convB e/2 (halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq e/2Pr) 0<e))
CauchyCompletion.converges (record { elts = a ; converges = convA } +C record { elts = b ; converges = convB }) ε 0<e | e/2 , e/2Pr | Na , prA | Nb , prB = (Na +N Nb) , t
  where
    t : {m n : ℕ} → Na +N Nb <N m → Na +N Nb <N n → abs ((index (apply _+_ a b) m) + inverse (index (apply _+_ a b) n)) < ε
    t {m} {n} <m <n with prA {m} {n} (inequalityShrinkLeft <m) (inequalityShrinkLeft <n)
    ... | am-an<e/2 with prB {m} {n} (inequalityShrinkRight <m) (inequalityShrinkRight <n)
    ... | bm-bn<e/2 with triangleInequality (index a m + inverse (index a n)) (index b m + inverse (index b n))
    ... | inl tri rewrite lemm m a b | lemm n a b = SetoidPartialOrder.<WellDefined pOrder (Equivalence.reflexive eq) e/2Pr (SetoidPartialOrder.transitive pOrder {_} {(abs ((index a m) + (inverse (index a n)))) + (abs ((index b m) + (inverse (index b n))))} (<WellDefined (absWellDefined _ _ (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index a m})) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq {index a m}) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index b m})) (+WellDefined (Equivalence.reflexive eq {index b m}) (Equivalence.symmetric eq (invContravariant additiveGroup)))))) (+Associative {index a m})))) (Equivalence.reflexive eq) tri) (ringAddInequalities am-an<e/2 bm-bn<e/2))
    ... | inr tri rewrite lemm m a b | lemm n a b = SetoidPartialOrder.<WellDefined pOrder (Equivalence.reflexive eq) e/2Pr (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq tri) (absWellDefined _ _ (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index a m})) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq {index a m}) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index b m})) (+WellDefined (Equivalence.reflexive eq {index b m}) (Equivalence.symmetric eq (invContravariant additiveGroup)))))) (+Associative {index a m}))))) (Equivalence.reflexive eq) (ringAddInequalities am-an<e/2 bm-bn<e/2))
