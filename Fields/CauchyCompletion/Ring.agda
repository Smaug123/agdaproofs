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
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Rings.Homomorphisms.Definition

module Fields.CauchyCompletion.Ring {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Field F
open Group (Ring.additiveGroup R)

open import Rings.Orders.Total.Lemmas order
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Multiplication order F
open import Fields.CauchyCompletion.Addition order F
open import Fields.CauchyCompletion.Setoid order F
open import Fields.CauchyCompletion.Group order F

private
  abstract
    c*Assoc : {a b c : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a *C (b *C c)) ((a *C b) *C c)
    c*Assoc {a} {b} {c} ε 0<e = 0 , ans
      where
        ans : {m : ℕ} → 0 <N m → abs (index (CauchyCompletion.elts ((a *C (b *C c)) +C (-C ((a *C b) *C c)))) m) < ε
        ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a *C (b *C c))) (CauchyCompletion.elts (-C ((a *C b) *C c))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)) _*_ {m} | equalityCommutative (mapAndIndex (apply _*_ (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (CauchyCompletion.elts c)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts c) _*_ {m} | indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (CauchyCompletion.elts c) _*_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _*_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (transferToRight'' (Ring.additiveGroup R) (Ring.*Associative R))) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

    c*Ident : {a : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (injection (Ring.1R R) *C a) a
    c*Ident {a} ε 0<e = 0 , ans
      where
        ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (injection (Ring.1R R) *C a)) (map inverse (CauchyCompletion.elts a))) m) < ε
        ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (injection (Ring.1R R) *C a)) (map inverse (CauchyCompletion.elts a)) _+_ {m} | indexAndApply (constSequence (Ring.1R R)) (CauchyCompletion.elts a) _*_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) | indexAndConst (Ring.1R R) m = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (transferToRight'' (Ring.additiveGroup R) (Ring.identIsIdent R))) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (absZero)))) (Equivalence.reflexive eq) 0<e

    *CDistribute : {a b c : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a *C (b +C c)) ((a *C b) +C (a *C c))
    *CDistribute {a} {b} {c} e 0<e = 0 , ans
      where
        ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (a *C (b +C c))) (map inverse (CauchyCompletion.elts ((a *C b) +C (a *C c))))) m) < e
        ans {m} N<m rewrite indexAndApply (CauchyCompletion.elts (a *C (b +C c))) (map inverse (CauchyCompletion.elts ((a *C b) +C (a *C c)))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (apply _+_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)) _*_ {m} | equalityCommutative (mapAndIndex (apply _+_ (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts c))) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts c) _+_ {m} | indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts c)) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _*_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts c) _*_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (transferToRight'' (Ring.additiveGroup R) (Ring.*DistributesOver+ R))) (absZeroIsZero))) (Equivalence.reflexive eq) 0<e

CRing : Ring cauchyCompletionSetoid _+C_ _*C_
Ring.additiveGroup CRing = CGroup
Ring.*WellDefined CRing {a} {b} {c} {d} r=t s=u = multiplicationWellDefined {a} {c} {b} {d} r=t s=u
Ring.1R CRing = injection (Ring.1R R)
Ring.groupIsAbelian CRing {a} {b} = +CCommutative {a} {b}
Ring.*Associative CRing {a} {b} {c} = c*Assoc {a} {b} {c}
Ring.*Commutative CRing {a} {b} = *CCommutative {a} {b}
Ring.*DistributesOver+ CRing {a} {b} {c} = *CDistribute {a} {b} {c}
Ring.identIsIdent CRing {a} = c*Ident {a}

private
  injectionIsRingHom : (a b : A) → Setoid._∼_ cauchyCompletionSetoid (injection (a * b)) (injection a *C injection b)
  injectionIsRingHom a b ε 0<e = 0 , ans
    where
      ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (injection (a * b))) (map inverse (CauchyCompletion.elts (injection a *C injection b)))) m) < ε
      ans {m} 0<m rewrite indexAndApply (constSequence (a * b)) (map inverse (apply _*_ (constSequence a) (constSequence b))) _+_ {m} | indexAndConst (a * b) m | equalityCommutative (mapAndIndex (apply _*_ (constSequence a) (constSequence b)) inverse m) | indexAndApply (constSequence a) (constSequence b) _*_ {m} | indexAndConst a m | indexAndConst b m = <WellDefined (symmetric (transitive (absWellDefined _ _ invRight) absZeroIsZero)) reflexive 0<e

CInjectionRingHom : RingHom R CRing injection
RingHom.preserves1 CInjectionRingHom = Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {injection (Ring.1R R)}
RingHom.ringHom CInjectionRingHom {a} {b} = injectionIsRingHom a b
RingHom.groupHom CInjectionRingHom = CInjectionGroupHom
