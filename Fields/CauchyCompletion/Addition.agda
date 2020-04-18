{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

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

module Fields.CauchyCompletion.Addition {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Ring R
open Group additiveGroup
open Field F

open import Fields.Lemmas F
open import Fields.CauchyCompletion.Definition order F
open import Rings.Orders.Partial.Lemmas pRing
open import Fields.Orders.Total.Lemmas {F = F} (record { oRing = order })
open import Rings.Orders.Total.AbsoluteValue order
open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.Cauchy order
open import Rings.InitialRing R

private
  lemm : (m : ℕ) (a b : Sequence A) → index (apply _+_ a b) m ≡ (index a m) + (index b m)
  lemm zero a b = refl
  lemm (succ m) a b = lemm m (Sequence.tail a) (Sequence.tail b)

private
  additionConverges : (a b : CauchyCompletion) → cauchy (apply _+_ (CauchyCompletion.elts a) (CauchyCompletion.elts b))
  additionConverges record { elts = a ; converges = convA } record { elts = b ; converges = convB } ε 0<e with halve charNot2 ε
  ... | e/2 , e/2Pr with convA e/2 (halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq e/2Pr) 0<e))
  ... | Na , prA with convB e/2 (halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq e/2Pr) 0<e))
  ... | Nb , prB = (Na +N Nb) , t
    where
      t : {m n : ℕ} → Na +N Nb <N m → Na +N Nb <N n → abs ((index (apply _+_ a b) m) + inverse (index (apply _+_ a b) n)) < ε
      t {m} {n} <m <n with prA {m} {n} (inequalityShrinkLeft <m) (inequalityShrinkLeft <n)
      ... | am-an<e/2 with prB {m} {n} (inequalityShrinkRight <m) (inequalityShrinkRight <n)
      ... | bm-bn<e/2 with triangleInequality (index a m + inverse (index a n)) (index b m + inverse (index b n))
      ... | inl tri rewrite lemm m a b | lemm n a b = SetoidPartialOrder.<WellDefined pOrder (Equivalence.reflexive eq) e/2Pr (SetoidPartialOrder.<Transitive pOrder {_} {(abs ((index a m) + (inverse (index a n)))) + (abs ((index b m) + (inverse (index b n))))} (<WellDefined (absWellDefined _ _ (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index a m})) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq {index a m}) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index b m})) (+WellDefined (Equivalence.reflexive eq {index b m}) (Equivalence.symmetric eq (invContravariant additiveGroup)))))) (+Associative {index a m})))) (Equivalence.reflexive eq) tri) (ringAddInequalities am-an<e/2 bm-bn<e/2))
      ... | inr tri rewrite lemm m a b | lemm n a b = SetoidPartialOrder.<WellDefined pOrder (Equivalence.reflexive eq) e/2Pr (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq tri) (absWellDefined _ _ (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index a m})) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq {index a m}) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq (+Associative {index b m})) (+WellDefined (Equivalence.reflexive eq {index b m}) (Equivalence.symmetric eq (invContravariant additiveGroup)))))) (+Associative {index a m}))))) (Equivalence.reflexive eq) (ringAddInequalities am-an<e/2 bm-bn<e/2))

_+C_ : CauchyCompletion → CauchyCompletion → CauchyCompletion
CauchyCompletion.elts (record { elts = a ; converges = convA } +C record { elts = b ; converges = convB }) = apply _+_ a b
CauchyCompletion.converges (a +C b) = additionConverges a b

inverseDistributes : {r s : A} → inverse (r + s) ∼ inverse r + inverse s
inverseDistributes = Equivalence.transitive eq (invContravariant additiveGroup) groupIsAbelian

-C_ : CauchyCompletion → CauchyCompletion
CauchyCompletion.elts (-C a) = map inverse (CauchyCompletion.elts a)
CauchyCompletion.converges (-C record { elts = elts ; converges = converges }) ε 0<e with converges ε 0<e
CauchyCompletion.converges (-C record { elts = elts ; converges = converges }) ε 0<e | N , prN = N , ans
  where
    ans : {m n : ℕ} → (N <N m) → (N <N n) → abs ((index (map inverse elts) m) + inverse (index (map inverse elts) n)) < ε
    ans {m} {n} N<m N<n = <WellDefined (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.reflexive eq)) (Equivalence.transitive eq (absNegation (index elts m + inverse (index elts n))) (absWellDefined _ _ (Equivalence.transitive eq inverseDistributes (+WellDefined (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (equalityCommutative (mapAndIndex elts inverse m))) (inverseWellDefined additiveGroup (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (equalityCommutative (mapAndIndex elts inverse n))))))))) (Equivalence.reflexive eq) (prN N<m N<n)
