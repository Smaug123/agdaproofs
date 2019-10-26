{-# OPTIONS --allow-unsolved-metas --warning=error --without-K --guardedness #-}

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

module Fields.CauchyCompletion.Ring {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder {_<_ = _<_} pOrder} {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Field F
open Group (Ring.additiveGroup R)

open import Rings.Orders.Lemmas(order)
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Multiplication order F charNot2
open import Fields.CauchyCompletion.Addition order F charNot2
open import Fields.CauchyCompletion.Setoid order F charNot2
open import Fields.CauchyCompletion.Group order F charNot2

c*Assoc : {a b c : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a *C (b *C c)) ((a *C b) *C c)
c*Assoc {a} {b} {c} ε 0<e = 0 , ans
  where
    ans : {m : ℕ} → 0 <N m → abs (index (CauchyCompletion.elts ((a *C (b *C c)) +C (-C ((a *C b) *C c)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a *C (b *C c))) (CauchyCompletion.elts (-C ((a *C b) *C c))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)) _*_ {m} | equalityCommutative (mapAndIndex (apply _*_ (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (CauchyCompletion.elts c)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts c) _*_ {m} | indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (CauchyCompletion.elts c) _*_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _*_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (transferToRight'' (Ring.additiveGroup R) (Ring.*Associative R))) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (absZero order)))) (Equivalence.reflexive eq) 0<e

c*Ident : {a : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (injection (Ring.1R R) *C a) a
c*Ident {a} ε 0<e = 0 , ans
  where
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (injection (Ring.1R R) *C a)) (map inverse (CauchyCompletion.elts a))) m) < ε
    ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (injection (Ring.1R R) *C a)) (map inverse (CauchyCompletion.elts a)) _+_ {m} | indexAndApply (constSequence (Ring.1R R)) (CauchyCompletion.elts a) _*_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) | indexAndConst (Ring.1R R) m = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (transferToRight'' (Ring.additiveGroup R) (Ring.identIsIdent R))) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (absZero order)))) (Equivalence.reflexive eq) 0<e

CRing : Ring cauchyCompletionSetoid _+C_ _*C_
Ring.additiveGroup CRing = CGroup
Ring.*WellDefined CRing {a} {b} {c} {d} r=t s=u = multiplicationWellDefined {a} {c} {b} {d} r=t s=u
Ring.1R CRing = injection (Ring.1R R)
Ring.groupIsAbelian CRing {a} {b} = +CCommutative {a} {b}
Ring.*Associative CRing {a} {b} {c} = c*Assoc {a} {b} {c}
Ring.*Commutative CRing {a} {b} = *CCommutative {a} {b}
Ring.*DistributesOver+ CRing = {!!}
Ring.identIsIdent CRing {a} = c*Ident {a}