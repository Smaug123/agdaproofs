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

module Fields.CauchyCompletion.Multiplication {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder {_<_ = _<_} pOrder} {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Ring R
open Group additiveGroup
open Field F

open import Rings.Orders.Lemmas(order)
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Setoid order F charNot2

_*C_ : CauchyCompletion → CauchyCompletion → CauchyCompletion
CauchyCompletion.elts (record { elts = a ; converges = aConv } *C record { elts = b ; converges = bConv }) = apply _*_ a b
CauchyCompletion.converges (record { elts = a ; converges = aConv } *C record { elts = b ; converges = bConv }) ε 0<e = {!!}

*CCommutative : {a b : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a *C b) (b *C a)
*CCommutative {a} {b} ε 0<e = 0 , ans
  where
    foo : {x y : A} → (x * y) + inverse (y * x) ∼ 0G
    foo = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (inverseWellDefined additiveGroup *Commutative)) invRight
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (a *C b)) (map inverse (CauchyCompletion.elts (b *C a)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts a))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _*_ {m} | equalityCommutative (mapAndIndex (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts a)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts a) _*_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ foo) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (absZero order)))) (Equivalence.reflexive eq) 0<e

multiplicationWellDefinedLeft : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C c)
multiplicationWellDefinedLeft a b c a=b ε 0<e = 0 , ans
  where
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts c)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)))) m) < ε
    ans {m} N<m rewrite indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts c)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c))) _+_ {m} | equalityCommutative (mapAndIndex (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts c) _*_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts c) _*_ {m} = {!!}

multiplicationPreservedLeft : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (injection a *C c) (injection b *C c)
multiplicationPreservedLeft {a} {b} {c} a=b = multiplicationWellDefinedLeft (injection a) (injection b) c (injectionPreservesSetoid a b a=b)

multiplicationPreservedRight : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (c *C injection a) (c *C injection b)
multiplicationPreservedRight {a} {b} {c} a=b = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {c *C injection a} {injection a *C c} {c *C injection b} (*CCommutative {c} {injection a}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a *C c} {injection b *C c} {c *C injection b} (multiplicationPreservedLeft {a} {b} {c} a=b) (*CCommutative {injection b} {c}))

multiplicationPreserved : {a b c d : A} → (a ∼ b) → (c ∼ d) → Setoid._∼_ cauchyCompletionSetoid (injection a *C injection c) (injection b *C injection d)
multiplicationPreserved {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a *C injection c} {injection a *C injection d} {injection b *C injection d} (multiplicationPreservedRight {c} {d} {injection a} c=d) (multiplicationPreservedLeft {a} {b} {injection d} a=b)

multiplicationWellDefinedRight : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid b c → Setoid._∼_ cauchyCompletionSetoid (a *C b) (a *C c)
multiplicationWellDefinedRight a b c b=c = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C b} {b *C a} {a *C c} (*CCommutative {a} {b}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {b *C a} {c *C a} {a *C c} (multiplicationWellDefinedLeft b c a b=c) (*CCommutative {c} {a}))

multiplicationWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C d)
multiplicationWellDefined {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C c} {a *C d} {b *C d} (multiplicationWellDefinedRight a c d c=d) (multiplicationWellDefinedLeft a b d a=b)
