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
open import Semirings.Definition

module Fields.CauchyCompletion.Setoid {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder {_<_ = _<_} pOrder} {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Ring R
open Group additiveGroup
open Field F

open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Addition order F charNot2
open import Rings.Orders.Lemmas(order)

isZero : CauchyCompletion → Set (m ⊔ o)
isZero record { elts = elts ; converges = converges } = ∀ ε → 0R < ε → Sg ℕ (λ N → ∀ {m : ℕ} → (N <N m) → (abs (index elts m)) < ε)

transitiveLemma : {a b c e/2 : A} → abs (a + inverse b) < e/2 → abs (b + inverse c) < e/2 → (abs (a + inverse c)) < (e/2 + e/2)
transitiveLemma {a} {b} {c} {e/2} a-b<e/2 b-c<e/2 with triangleInequality (a + inverse b) (b + inverse c)
transitiveLemma {a} {b} {c} {e/2} a-b<e/2 b-c<e/2 | inl x = SetoidPartialOrder.transitive pOrder (<WellDefined (absWellDefined _ _ (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq +Associative (Equivalence.transitive eq (+WellDefined invLeft (Equivalence.reflexive eq)) identLeft))))) (Equivalence.reflexive eq) x) (ringAddInequalities a-b<e/2 b-c<e/2)
transitiveLemma {a} {b} {c} {e/2} a-b<e/2 b-c<e/2 | inr x = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.symmetric eq ((Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq +Associative (Equivalence.transitive eq (+WellDefined invLeft (Equivalence.reflexive eq)) identLeft))))))) x)) (Equivalence.reflexive eq) (ringAddInequalities a-b<e/2 b-c<e/2)

cauchyCompletionSetoid : Setoid CauchyCompletion
(cauchyCompletionSetoid Setoid.∼ a) b = isZero (a +C (-C b))
Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {x} ε 0<e = 0 , t
  where
    t : {m : ℕ} → (0 <N m) → abs (index (apply _+_ (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts x))) m) < ε
    t {m} 0<m rewrite indexAndApply (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts x)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts x) inverse m) = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ invRight) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (absZero order)))) (Equivalence.reflexive eq) 0<e
Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {x} {y} x=y ε 0<e with x=y ε 0<e
Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {x} {y} x=y ε 0<e | N , pr = N , t
  where
    t : {m : ℕ} → N <N m → abs (index (apply _+_ (CauchyCompletion.elts y) (map inverse (CauchyCompletion.elts x))) m) < ε
    t {m} N<m = <WellDefined (Equivalence.transitive eq (absNegation _) (absWellDefined _ _ (identityOfIndiscernablesRight _∼_ (identityOfIndiscernablesLeft _∼_ (identityOfIndiscernablesLeft _∼_ (Equivalence.transitive eq (inverseDistributes) (Equivalence.transitive eq groupIsAbelian (+WellDefined (Equivalence.transitive eq (inverseWellDefined additiveGroup (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (mapAndIndex _ inverse m))) (invTwice additiveGroup (index (CauchyCompletion.elts y) m))) (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (equalityCommutative (mapAndIndex (CauchyCompletion.elts x) inverse m)))))) (equalityCommutative (mapAndApply (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts y)) _+_ inverse m))) (equalityCommutative (mapAndIndex _ inverse m))) (equalityCommutative (indexAndApply (CauchyCompletion.elts y) (map inverse (CauchyCompletion.elts x)) _+_ {m}))))) (Equivalence.reflexive eq) (pr N<m)
Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {x} {y} {z} x=y y=z ε 0<e with halve ε
... | e/2 , prHalf with x=y e/2 (halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prHalf) 0<e))
... | Nx , prX with y=z e/2 (halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prHalf) 0<e))
... | Ny , prY = (Nx +N Ny) , t
  where
    t : {m : ℕ} → (Nx +N Ny <N m) → abs (index (apply _+_ (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts z))) m) < ε
    t {m} nsPr with prX {m} (le (_<N_.x nsPr +N Ny) (transitivity (applyEquality succ (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring _ Ny Nx)) (applyEquality ( λ i → (_<N_.x nsPr) +N i) (Semiring.commutative ℕSemiring Ny Nx)))) (_<N_.proof nsPr)))
    ... | x-y<e/2 with prY {m} (le (_<N_.x nsPr +N Nx) (transitivity (applyEquality succ (equalityCommutative (Semiring.+Associative ℕSemiring _ Nx Ny))) (_<N_.proof nsPr)))
    ... | y-z<e/2 rewrite indexAndApply (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts z)) _+_ {m} | indexAndApply (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts y)) _+_ {m} | indexAndApply (CauchyCompletion.elts y) (map inverse (CauchyCompletion.elts z)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts z) inverse m) | equalityCommutative (mapAndIndex (CauchyCompletion.elts y) inverse m) = <WellDefined (Equivalence.reflexive eq) prHalf (transitiveLemma x-y<e/2 y-z<e/2)

injectionPreservesSetoid : (a b : A) → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (injection a) (injection b)
injectionPreservesSetoid a b a=b ε 0<e = 0 , t
  where
    t : {m : ℕ} → 0 <N m → abs (index (apply _+_ (constSequence a) (map inverse (constSequence b))) m) < ε
    t {m} 0<m = <WellDefined (identityOfIndiscernablesLeft _∼_ (absWellDefined 0G _ (identityOfIndiscernablesRight _∼_ (Equivalence.transitive eq (Equivalence.symmetric eq (transferToRight'' additiveGroup a=b)) (+WellDefined (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (indexAndConst a m)) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (transitivity (applyEquality inverse (equalityCommutative (indexAndConst _ m))) (mapAndIndex _ inverse m))))) (equalityCommutative (indexAndApply (constSequence a) _ _+_ {m})))) (absZero order)) (Equivalence.reflexive eq) 0<e

absZeroImpliesZero : {a : A} → abs a ∼ 0R → a ∼ 0R
absZeroImpliesZero {a} a=0 with totality 0R a
absZeroImpliesZero {a} a=0 | inl (inl 0<a) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) a=0 0<a))
absZeroImpliesZero {a} a=0 | inl (inr a<0) = Equivalence.symmetric eq (lemm3 (inverse a) a (Equivalence.symmetric eq invLeft) (Equivalence.symmetric eq a=0))
absZeroImpliesZero {a} a=0 | inr 0=a = a=0

a-bPos : {a b : A} → ((a ∼ b) → False) → 0R < abs (a + inverse b)
a-bPos {a} {b} a!=b with totality 0R (a + inverse b)
a-bPos {a} {b} a!=b | inl (inl x) = x
a-bPos {a} {b} a!=b | inl (inr x) = lemm2 _ x
a-bPos {a} {b} a!=b | inr x = exFalso (a!=b (transferToRight additiveGroup (Equivalence.symmetric eq x)))

injectionPreservesSetoid' : (a b : A) → ((a ∼ b) → False) → Setoid._∼_ cauchyCompletionSetoid (injection a) (injection b) → False
injectionPreservesSetoid' a b (a!=b) a=b with halve (abs (a + inverse b))
... | a-b/2 , pr with a=b a-b/2 (halvePositive a-b/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr) (a-bPos a!=b)))
... | N , pr2 with pr2 {m = succ N} (le 0 refl)
... | a-b<a-b/2 rewrite indexAndApply (constSequence a) (map inverse (constSequence b)) _+_ {N} | indexAndConst a N | equalityCommutative (mapAndIndex (constSequence b) inverse N) | indexAndConst b N = SetoidPartialOrder.irreflexive pOrder v
  where
    t : (abs (a + inverse b) + abs (a + inverse b)) < abs (a + inverse b)
    t = <WellDefined (Equivalence.reflexive eq) pr (ringAddInequalities a-b<a-b/2 a-b<a-b/2)
    u : 0R < abs (a + inverse b)
    u = a-bPos a!=b
    v : (abs (a + inverse b) + abs (a + inverse b)) < (abs (a + inverse b) + abs (a + inverse b))
    v = SetoidPartialOrder.transitive pOrder t (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition u (abs (a + inverse b))))

additionWellDefinedLeft : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a +C c) (b +C c)
additionWellDefinedLeft a b c a=b ε 0<e = {!!}

additionWellDefinedRight : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid b c → Setoid._∼_ cauchyCompletionSetoid (a +C b) (a +C c)
additionWellDefinedRight a b c a=b ε 0<e = {!!}

additionWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → Setoid._∼_ cauchyCompletionSetoid (a +C c) (b +C d)
additionWellDefined {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a +C c} {a +C d} {b +C d} (additionWellDefinedRight a c d c=d) (additionWellDefinedLeft a b d a=b)
