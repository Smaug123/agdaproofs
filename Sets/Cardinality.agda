{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Sets.Cardinality.Finite.Definition
open import Semirings.Definition
open import Sets.CantorBijection.CantorBijection
open import Orders.Total.Definition

module Sets.Cardinality where

open import Semirings.Lemmas ℕSemiring

record CountablyInfiniteSet {a : _} (A : Set a) : Set a where
  field
    counting : A → ℕ
    countingIsBij : Bijection counting

data Countable {a : _} (A : Set a) : Set a where
  finite : FiniteSet A → Countable A
  infinite : CountablyInfiniteSet A → Countable A

ℕCountable : CountablyInfiniteSet ℕ
ℕCountable = record { counting = id ; countingIsBij = invertibleImpliesBijection (record { inverse = id ; isLeft = λ b → refl ; isRight = λ a → refl}) }

doubleLemma : (a b : ℕ) → 2 *N a ≡ 2 *N b → a ≡ b
doubleLemma a b pr = productCancelsLeft 2 a b (le 1 refl) pr

evenCannotBeOdd : (a b : ℕ) → 2 *N a ≡ succ (2 *N b) → False
evenCannotBeOdd zero b ()
evenCannotBeOdd (succ a) zero pr rewrite Semiring.commutative ℕSemiring a 0 | Semiring.commutative ℕSemiring a (succ a) = naughtE (equalityCommutative (succInjective pr))
evenCannotBeOdd (succ a) (succ b) pr = evenCannotBeOdd a b pr''
  where
    pr' : a +N a ≡ (b +N succ b)
    pr' rewrite Semiring.commutative ℕSemiring a 0 | Semiring.commutative ℕSemiring b 0 | Semiring.commutative ℕSemiring a (succ a) = succInjective (succInjective pr)
    pr'' : 2 *N a ≡ succ (2 *N b)
    pr'' rewrite Semiring.commutative ℕSemiring a 0 | Semiring.commutative ℕSemiring b 0 | Semiring.commutative ℕSemiring (succ b) b = pr'

aMod2 : (a : ℕ) → Sg ℕ (λ i → (2 *N i ≡ a) || (succ (2 *N i) ≡ a))
aMod2 zero = (0 , inl refl)
aMod2 (succ a) with aMod2 a
aMod2 (succ a) | b , inl x = b , inr (applyEquality succ x)
aMod2 (succ a) | b , inr x = (succ b) , inl pr
  where
    pr : succ (b +N succ (b +N 0)) ≡ succ a
    pr rewrite Semiring.commutative ℕSemiring b (succ (b +N 0)) | Semiring.commutative ℕSemiring (b +N 0) b = applyEquality succ x

sqrtFloor : (a : ℕ) → Sg (ℕ && ℕ) (λ pair → ((_&&_.fst pair) *N (_&&_.fst pair) +N (_&&_.snd pair) ≡ a) && ((_&&_.snd pair) <N 2 *N (_&&_.fst pair) +N 1))
sqrtFloor zero = (0 ,, 0) , (refl ,, le zero refl)
sqrtFloor (succ n) with sqrtFloor n
sqrtFloor (succ n) | (a ,, b) , pr with TotalOrder.totality ℕTotalOrder b (2 *N a)
sqrtFloor (succ n) | (a ,, b) , pr | inl (inl x) = (a ,, succ b) , (p ,, q)
  where
    p : a *N a +N succ b ≡ succ n
    p rewrite Semiring.commutative ℕSemiring (a *N a) (succ b) | Semiring.commutative ℕSemiring b (a *N a) = applyEquality succ (_&&_.fst pr)
    q : succ b <N (a +N (a +N 0)) +N 1
    q rewrite Semiring.commutative ℕSemiring (a +N (a +N 0)) (succ 0) | Semiring.commutative ℕSemiring a 0 = succPreservesInequality x
sqrtFloor (succ n) | (a ,, b) , (_ ,, pr) | inl (inr x) rewrite Semiring.commutative ℕSemiring (a +N (a +N 0)) (succ 0) = exFalso (noIntegersBetweenXAndSuccX (a +N (a +N 0)) x pr)
sqrtFloor (succ n) | (a ,, b) , pr | inr x = (succ a ,, 0) , (q ,, succIsPositive _)
  where
    p : a +N a *N succ a ≡ n
    p rewrite x | Semiring.commutative ℕSemiring a 0 | Semiring.commutative ℕSemiring (a +N a) (succ 0) | Semiring.commutative ℕSemiring (a *N a) (succ a +N a) | multiplicationNIsCommutative a (succ a) | Semiring.commutative ℕSemiring (a *N a) (a +N a) | Semiring.+Associative ℕSemiring a a (a *N a) = _&&_.fst pr
    q : succ ((a +N a *N succ a) +N 0) ≡ succ n
    q rewrite Semiring.commutative ℕSemiring (a +N a *N succ a) 0 = applyEquality succ p

pairUnionIsCountable : {a b : _} {A : Set a} {B : Set b} → (X : CountablyInfiniteSet A) → (Y : CountablyInfiniteSet B) → CountablyInfiniteSet (A || B)
CountablyInfiniteSet.counting (pairUnionIsCountable X Y) (inl r) = 2 *N (CountablyInfiniteSet.counting X r)
CountablyInfiniteSet.counting (pairUnionIsCountable X Y) (inr s) = succ (2 *N (CountablyInfiniteSet.counting Y s))
Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) {inl x} {inl y} pr rewrite Semiring.commutative ℕSemiring (CountablyInfiniteSet.counting X x) 0 | Semiring.commutative ℕSemiring (CountablyInfiniteSet.counting X y) 0 | doubleIsAddTwo (CountablyInfiniteSet.counting X x) | doubleIsAddTwo (CountablyInfiniteSet.counting X y) = applyEquality inl (Bijection.inj (CountablyInfiniteSet.countingIsBij X) inter)
  where
    inter : CountablyInfiniteSet.counting X x ≡ CountablyInfiniteSet.counting X y
    inter = doubleLemma (CountablyInfiniteSet.counting X x) (CountablyInfiniteSet.counting X y) pr
Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) {inl x} {inr y} pr = exFalso (evenCannotBeOdd (CountablyInfiniteSet.counting X x) (CountablyInfiniteSet.counting Y y) pr)
Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) {inr x} {inl y} pr = exFalso (evenCannotBeOdd (CountablyInfiniteSet.counting X y) (CountablyInfiniteSet.counting Y x) (equalityCommutative pr))
Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) {inr x} {inr y} pr = applyEquality inr (Bijection.inj (CountablyInfiniteSet.countingIsBij Y) (doubleLemma (CountablyInfiniteSet.counting Y x) (CountablyInfiniteSet.counting Y y) (succInjective pr) ))
Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) b with aMod2 b
Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) b | a , inl x with Bijection.surj (CountablyInfiniteSet.countingIsBij X) a
Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) b | a , inl x | r , pr = inl r , ans
  where
    ans : 2 *N CountablyInfiniteSet.counting X r ≡ b
    ans rewrite pr = x
Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) b | a , inr x with Bijection.surj (CountablyInfiniteSet.countingIsBij Y) a
Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y)) b | a , inr x | r , pr = inr r , ans
  where
    ans : succ (2 *N CountablyInfiniteSet.counting Y r) ≡ b
    ans rewrite pr = x

firstEqualityOfPair : {a b : _} {A : Set a} {B : Set b} → {x1 x2 : A} → {y1 y2 : B} → (x1 ,, y1) ≡ (x2 ,, y2) → x1 ≡ x2
firstEqualityOfPair {x1} {x2} {y1} {y2} refl = refl

secondEqualityOfPair : {a b : _} {A : Set a} {B : Set b} → {x1 x2 : A} → {y1 y2 : B} → (x1 ,, y1) ≡ (x2 ,, y2) → y1 ≡ y2
secondEqualityOfPair {x1} {x2} {y1} {y2} refl = refl

reflPair : {a b : _} {A : Set a} {B : Set b} {x1 x2 : A} {y1 y2 : B} → (x1 ≡ x2) → (y1 ≡ y2) → (x1 ,, y1) ≡ x2 ,, y2
reflPair refl refl = refl

bijectionOfCountableSetIsCountable : {a b : _} {A : Set a} {B : Set b} → (X : CountablyInfiniteSet A) {f : A → B} → (bij : Bijection f) → CountablyInfiniteSet B
CountablyInfiniteSet.counting (bijectionOfCountableSetIsCountable X {f} record { inj = inj ; surj = surj }) b with surj b
CountablyInfiniteSet.counting (bijectionOfCountableSetIsCountable record { counting = counting ; countingIsBij = countingIsBij } {f} record { inj = inj ; surj = surj }) b | a , pr = counting a
Bijection.inj (CountablyInfiniteSet.countingIsBij (bijectionOfCountableSetIsCountable X {f} record { inj = inj ; surj = surj })) {m} {n} m=n with surj m
Bijection.inj (CountablyInfiniteSet.countingIsBij (bijectionOfCountableSetIsCountable X {f} record { inj = inj ; surj = surj })) {m} {n} m=n | a , b with surj n
... | c , d = transitivity (equalityCommutative b) (transitivity (applyEquality f (Bijection.inj (CountablyInfiniteSet.countingIsBij X) m=n)) d)
Bijection.surj (CountablyInfiniteSet.countingIsBij (bijectionOfCountableSetIsCountable X {f} record { inj = inj ; surj = surj })) b with Bijection.surj (CountablyInfiniteSet.countingIsBij X) b
Bijection.surj (CountablyInfiniteSet.countingIsBij (bijectionOfCountableSetIsCountable X {f} record { inj = inj ; surj = surj })) b | a , pr = f a , s
  where
    s : CountablyInfiniteSet.counting (bijectionOfCountableSetIsCountable X {f} record { inj = inj ; surj = surj }) (f a) ≡ b
    s with surj (f a)
    s | t , u = transitivity (applyEquality (CountablyInfiniteSet.counting X) (inj u)) pr

N^2Countable : CountablyInfiniteSet (ℕ && ℕ)
CountablyInfiniteSet.counting N^2Countable x = Invertible.inverse (bijectionImpliesInvertible (cantorBijection)) x
CountablyInfiniteSet.countingIsBij N^2Countable = invertibleImpliesBijection (inverseIsInvertible (bijectionImpliesInvertible cantorBijection))

tupleRmap : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → (f : B → C) → (A && B) → (A && C)
tupleRmap f (a ,, b) = (a ,, f b)

tupleLmap : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → (f : A → C) → (A && B) → (C && B)
tupleLmap f (a ,, b) = (f a ,, b)

bijectionOnRightOfProduct : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → {f : B → C} → Bijection f → Bijection (tupleRmap {A = A} f)
Bijection.inj (bijectionOnRightOfProduct {A = A} {B} {C} {f} bij) {fst ,, snd} {fst₁ ,, snd₁} gx=gy rewrite firstEqualityOfPair gx=gy | Bijection.inj bij (secondEqualityOfPair gx=gy) = refl
Bijection.surj (bijectionOnRightOfProduct {A = A} {B} {C} {f} bij) (fst ,, snd) with Bijection.surj bij snd
Bijection.surj (bijectionOnRightOfProduct {A = A} {B} {C} {f} bij) (fst ,, snd) | b , pr = (fst ,, b) , reflPair refl pr

bijectionOnLeftOfProduct : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → {f : A → C} → Bijection f → Bijection (tupleLmap {B = B} f)
Bijection.inj (bijectionOnLeftOfProduct {A = A} {B} {C} {f} bij) {a ,, b} {c ,, d} gx=gy rewrite secondEqualityOfPair gx=gy | Bijection.inj bij (firstEqualityOfPair gx=gy) = refl
Bijection.surj (bijectionOnLeftOfProduct {A = A} {B} {C} {f} bij) (fst ,, snd) with Bijection.surj bij fst
Bijection.surj (bijectionOnLeftOfProduct {A = A} {B} {C} {f} bij) (fst ,, snd) | a , b = (a ,, snd) , reflPair b refl

pairProductIsCountable : {a b : _} {A : Set a} {B : Set b} → (X : CountablyInfiniteSet A) → (Y : CountablyInfiniteSet B) → CountablyInfiniteSet (A && B)
pairProductIsCountable {A = A} {B = B} X Y = bijectionOfCountableSetIsCountable N^2Countable {(tupleLmap m) ∘ (tupleRmap n)} bijF
  where
    bijM = (bijectionImpliesInvertible (CountablyInfiniteSet.countingIsBij X))
    bijN = (bijectionImpliesInvertible (CountablyInfiniteSet.countingIsBij Y))
    m : ℕ → A
    m = Invertible.inverse bijM
    n : ℕ → B
    n = Invertible.inverse bijN
    bM : Bijection m
    bM = invertibleImpliesBijection (record { inverse = CountablyInfiniteSet.counting X ; isLeft = Invertible.isRight bijM ; isRight = Invertible.isLeft bijM })
    bN : Bijection n
    bN = invertibleImpliesBijection (record { inverse = CountablyInfiniteSet.counting Y ; isLeft = Invertible.isRight bijN ; isRight = Invertible.isLeft bijN })
    bijF : Bijection ((tupleLmap {A = ℕ} {B = B} {C = A} m) ∘ (tupleRmap {A = ℕ} {B = ℕ} {C = B} n))
    bijF = bijectionComp {f = tupleRmap {A = ℕ} {B = ℕ} {C = B} n} {g = tupleLmap {A = ℕ} {B = B} {C = A} m} (bijectionOnRightOfProduct (invertibleImpliesBijection (bijectionImpliesInvertible bN))) (bijectionOnLeftOfProduct bM)

--  injectionToNMeansCountable : {a : _} {A : Set a} {f : A → ℕ} → Injection f → InfiniteSet A → Countable A
--  injectionToNMeansCountable {f = f} inj record { isInfinite = isInfinite } = {!!}
