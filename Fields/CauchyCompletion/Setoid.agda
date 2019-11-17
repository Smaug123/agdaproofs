{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Groups
open import Groups.Lemmas
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Semirings.Definition

module Fields.CauchyCompletion.Setoid {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

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
open import Fields.CauchyCompletion.Addition order F charNot2
open import Rings.Orders.Partial.Lemmas pRing
open import Rings.Orders.Total.Lemmas order

isZero : CauchyCompletion → Set (m ⊔ o)
isZero record { elts = elts ; converges = converges } = ∀ ε → 0R < ε → Sg ℕ (λ N → ∀ {m : ℕ} → (N <N m) → (abs (index elts m)) < ε)

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

+CCommutative : {a b : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a +C b) (b +C a)
+CCommutative {a} {b} ε 0<e = 0 , ans
  where
    foo : {x y : A} → (x + y) + inverse (y + x) ∼ 0G
    foo = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (inverseWellDefined additiveGroup groupIsAbelian)) invRight
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (a +C b)) (map inverse (CauchyCompletion.elts (b +C a)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a +C b)) (map inverse (CauchyCompletion.elts (b +C a))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _+_ {m} | equalityCommutative (mapAndIndex (apply _+_ (CauchyCompletion.elts b) (CauchyCompletion.elts a)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts a) _+_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ foo) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

additionWellDefinedLeft : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a +C c) (b +C c)
additionWellDefinedLeft record { elts = a ; converges = aConv } record { elts = b ; converges = bConv } record { elts = c ; converges = cConv } a=b ε 0<e with a=b ε 0<e
... | Na-b , prA-b = Na-b , ans
  where
    ans : {m : ℕ} → Na-b <N m → abs (index (apply _+_ (apply _+_ a c) (map inverse (apply _+_ b c))) m) < ε
    ans {m} mBig with prA-b {m} mBig
    ... | bl rewrite indexAndApply (apply _+_ a c) (map inverse (apply _+_ b c)) _+_ {m} | indexAndApply a c _+_ {m} | equalityCommutative (mapAndIndex (apply _+_ b c) inverse m) | indexAndApply b c _+_ {m} = <WellDefined (absWellDefined _ _ t) (Equivalence.reflexive eq) bl
      where
        t : index (apply _+_ a (map inverse b)) m ∼ ((index a m + index c m) + inverse (index b m + index c m))
        t rewrite indexAndApply a (map inverse b) _+_ {m} | equalityCommutative (mapAndIndex b inverse m) = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq identLeft) (+WellDefined (Equivalence.symmetric eq invRight) (Equivalence.reflexive eq))) (Equivalence.symmetric eq +Associative)) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (invContravariant additiveGroup))))) (+Associative {index a m})

additionPreservedLeft : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (injection a +C c) (injection b +C c)
additionPreservedLeft {a} {b} {c} a=b = additionWellDefinedLeft (injection a) (injection b) c (injectionPreservesSetoid a b a=b)

additionPreservedRight : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (c +C injection a) (c +C injection b)
additionPreservedRight {a} {b} {c} a=b = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {c +C injection a} {injection a +C c} {c +C injection b} (+CCommutative {c} {injection a}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a +C c} {injection b +C c} {c +C injection b} (additionPreservedLeft {a} {b} {c} a=b) (+CCommutative {injection b} {c}))

additionPreserved : {a b c d : A} → (a ∼ b) → (c ∼ d) → Setoid._∼_ cauchyCompletionSetoid (injection a +C injection c) (injection b +C injection d)
additionPreserved {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a +C injection c} {injection a +C injection d} {injection b +C injection d} (additionPreservedRight {c} {d} {injection a} c=d) (additionPreservedLeft {a} {b} {injection d} a=b)

additionWellDefinedRight : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid b c → Setoid._∼_ cauchyCompletionSetoid (a +C b) (a +C c)
additionWellDefinedRight a b c b=c = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a +C b} {b +C a} {a +C c} (+CCommutative {a} {b}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {b +C a} {c +C a} {a +C c} (additionWellDefinedLeft b c a b=c) (+CCommutative {c} {a}))

additionWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → Setoid._∼_ cauchyCompletionSetoid (a +C c) (b +C d)
additionWellDefined {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a +C c} {a +C d} {b +C d} (additionWellDefinedRight a c d c=d) (additionWellDefinedLeft a b d a=b)

additionHom : (x y : A) → Setoid._∼_ cauchyCompletionSetoid (injection (x + y)) (injection x +C injection y)
additionHom x y ε 0<e = 0 , ans
  where
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (injection (x + y))) (map inverse (CauchyCompletion.elts (injection x +C injection y)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (injection (x + y))) (map inverse (CauchyCompletion.elts (injection x +C injection y))) _+_ {m} | equalityCommutative (mapAndIndex (apply _+_ (constSequence x) (constSequence y)) inverse m) | indexAndConst (x + y) m | indexAndApply (constSequence x) (constSequence y) _+_ {m} | indexAndConst x m | indexAndConst y m = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ invRight) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

CInjection : SetoidInjection S cauchyCompletionSetoid injection
SetoidInjection.wellDefined CInjection {x} {y} x=y = injectionPreservesSetoid x y x=y
SetoidInjection.injective CInjection {x} {y} x=y = injectionPreservesSetoid' x y x=y

trivialIfInputTrivial : (0R ∼ 1R) → (a : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid (injection 0R) a
trivialIfInputTrivial 0=1 a ε 0<e = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (oneZeroImpliesAllZero R 0=1) 0<e))
