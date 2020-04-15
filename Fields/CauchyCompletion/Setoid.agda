{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
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
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Semirings.Definition

module Fields.CauchyCompletion.Setoid {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

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
open import Fields.CauchyCompletion.Addition order F
open import Rings.Orders.Partial.Lemmas pRing
open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.AbsoluteValue order
open import Rings.InitialRing R
open import Fields.Orders.Total.Lemmas {F = F} (record { oRing = order })

isZero : CauchyCompletion → Set (m ⊔ o)
isZero record { elts = elts ; converges = converges } = ∀ ε → 0R < ε → Sg ℕ (λ N → ∀ {m : ℕ} → (N <N m) → (abs (index elts m)) < ε)

private
  transitiveLemma : {a b c e/2 : A} → abs (a + inverse b) < e/2 → abs (b + inverse c) < e/2 → (abs (a + inverse c)) < (e/2 + e/2)
  transitiveLemma {a} {b} {c} {e/2} a-b<e/2 b-c<e/2 with triangleInequality (a + inverse b) (b + inverse c)
  transitiveLemma {a} {b} {c} {e/2} a-b<e/2 b-c<e/2 | inl x = SetoidPartialOrder.<Transitive pOrder (<WellDefined (absWellDefined _ _ (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq +Associative (Equivalence.transitive eq (+WellDefined invLeft (Equivalence.reflexive eq)) identLeft))))) (Equivalence.reflexive eq) x) (ringAddInequalities a-b<e/2 b-c<e/2)
  transitiveLemma {a} {b} {c} {e/2} a-b<e/2 b-c<e/2 | inr x = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.symmetric eq ((Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq +Associative (Equivalence.transitive eq (+WellDefined invLeft (Equivalence.reflexive eq)) identLeft))))))) x)) (Equivalence.reflexive eq) (ringAddInequalities a-b<e/2 b-c<e/2)

cauchyCompletionSetoid : Setoid CauchyCompletion
(cauchyCompletionSetoid Setoid.∼ a) b = isZero (a +C (-C b))
Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {x} ε 0<e = 0 , t
  where
    t : {m : ℕ} → (0 <N m) → abs (index (apply _+_ (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts x))) m) < ε
    t {m} 0<m rewrite indexAndApply (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts x)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts x) inverse m) = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ invRight) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e
Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {x} {y} x=y ε 0<e with x=y ε 0<e
Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {x} {y} x=y ε 0<e | N , pr = N , t
  where
    t : {m : ℕ} → N <N m → abs (index (apply _+_ (CauchyCompletion.elts y) (map inverse (CauchyCompletion.elts x))) m) < ε
    t {m} N<m = <WellDefined (Equivalence.transitive eq (absNegation _) (absWellDefined _ _ (identityOfIndiscernablesRight _∼_ (identityOfIndiscernablesLeft _∼_ (identityOfIndiscernablesLeft _∼_ (Equivalence.transitive eq (inverseDistributes) (Equivalence.transitive eq groupIsAbelian (+WellDefined (Equivalence.transitive eq (inverseWellDefined additiveGroup (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (mapAndIndex _ inverse m))) (invTwice additiveGroup (index (CauchyCompletion.elts y) m))) (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (equalityCommutative (mapAndIndex (CauchyCompletion.elts x) inverse m)))))) (equalityCommutative (mapAndApply (CauchyCompletion.elts x) (map inverse (CauchyCompletion.elts y)) _+_ inverse m))) (equalityCommutative (mapAndIndex _ inverse m))) (equalityCommutative (indexAndApply (CauchyCompletion.elts y) (map inverse (CauchyCompletion.elts x)) _+_ {m}))))) (Equivalence.reflexive eq) (pr N<m)
Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {x} {y} {z} x=y y=z ε 0<e with halve charNot2 ε
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
    t {m} 0<m = <WellDefined (identityOfIndiscernablesLeft _∼_ (absWellDefined 0G _ (identityOfIndiscernablesRight _∼_ (Equivalence.transitive eq (Equivalence.symmetric eq (transferToRight'' additiveGroup a=b)) (+WellDefined (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (indexAndConst a m)) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (transitivity (applyEquality inverse (equalityCommutative (indexAndConst _ m))) (mapAndIndex _ inverse m))))) (equalityCommutative (indexAndApply (constSequence a) _ _+_ {m})))) absZero) (Equivalence.reflexive eq) 0<e

infinitesimalImplies0 : (a : A) → ({ε : A} → (0R < ε) → a < ε) → (a ∼ 0R) || (a < 0R)
infinitesimalImplies0 a pr with totality 0R a
infinitesimalImplies0 a pr | inl (inl 0<a) with halve charNot2 a
infinitesimalImplies0 a pr | inl (inl 0<a) | a/2 , prA/2 with pr {a/2} (halvePositive a/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prA/2) 0<a))
... | bl with halvePositive a/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prA/2) 0<a)
... | 0<a/2 = exFalso (irreflexive {a} (<WellDefined identLeft prA/2 (ringAddInequalities 0<a/2 bl)))
infinitesimalImplies0 a pr | inl (inr a<0) = inr a<0
infinitesimalImplies0 a pr | inr 0=a = inl (Equivalence.symmetric eq 0=a)

injectionPreservesSetoid' : (a b : A) → Setoid._∼_ cauchyCompletionSetoid (injection a) (injection b) → a ∼ b
injectionPreservesSetoid' a b a=b = transferToRight additiveGroup (absZeroImpliesZero ans)
  where
    infinitesimal : {ε : A} → 0G < ε → abs (a + inverse b) < ε
    infinitesimal {ε} 0<e with a=b ε 0<e
    ... | N , pr with pr {succ N} (le 0 refl)
    ... | bl rewrite indexAndApply (constSequence a) (map inverse (constSequence b)) _+_ {N} | indexAndConst a N | equalityCommutative (mapAndIndex (constSequence b) inverse N) | indexAndConst b N = bl
    ans : (abs (a + inverse b)) ∼ 0G
    ans with infinitesimalImplies0 _ infinitesimal
    ... | inl x = x
    ... | inr x = exFalso (absNonnegative x)

CInjection : SetoidInjection S cauchyCompletionSetoid injection
SetoidInjection.wellDefined CInjection {x} {y} x=y = injectionPreservesSetoid x y x=y
SetoidInjection.injective CInjection {x} {y} x=y = injectionPreservesSetoid' x y x=y

trivialIfInputTrivial : (0R ∼ 1R) → (a : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid (injection 0R) a
trivialIfInputTrivial 0=1 a ε 0<e = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (oneZeroImpliesAllZero R 0=1) 0<e))
