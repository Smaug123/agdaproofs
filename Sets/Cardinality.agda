{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Semirings.Definition
open import Orders
open import WellFoundedInduction
open import Sets.CantorBijection.CantorBijection

module Sets.Cardinality where
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
  sqrtFloor (succ n) | (a ,, b) , pr with orderIsTotal b (2 *N a)
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
  Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) {inl x} {inl y} pr rewrite Semiring.commutative ℕSemiring (CountablyInfiniteSet.counting X x) 0 | Semiring.commutative ℕSemiring (CountablyInfiniteSet.counting X y) 0 | doubleIsAddTwo (CountablyInfiniteSet.counting X x) | doubleIsAddTwo (CountablyInfiniteSet.counting X y) = applyEquality inl (Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij X)) inter)
    where
      inter : CountablyInfiniteSet.counting X x ≡ CountablyInfiniteSet.counting X y
      inter = doubleLemma (CountablyInfiniteSet.counting X x) (CountablyInfiniteSet.counting X y) pr
  Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) {inl x} {inr y} pr = exFalso (evenCannotBeOdd (CountablyInfiniteSet.counting X x) (CountablyInfiniteSet.counting Y y) pr)
  Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) {inr x} {inl y} pr = exFalso (evenCannotBeOdd (CountablyInfiniteSet.counting X y) (CountablyInfiniteSet.counting Y x) (equalityCommutative pr))
  Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) {inr x} {inr y} pr = applyEquality inr (Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij Y)) (doubleLemma (CountablyInfiniteSet.counting Y x) (CountablyInfiniteSet.counting Y y) (succInjective pr) ))
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) b with aMod2 b
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) b | a , inl x with Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij X)) a
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) b | a , inl x | r , pr = inl r , ans
    where
      ans : 2 *N CountablyInfiniteSet.counting X r ≡ b
      ans rewrite pr = x
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) b | a , inr x with Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij Y)) a
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairUnionIsCountable X Y))) b | a , inr x | r , pr = inr r , ans
    where
      ans : succ (2 *N CountablyInfiniteSet.counting Y r) ≡ b
      ans rewrite pr = x

  firstEqualityOfPair : {a b : _} {A : Set a} {B : Set b} → {x1 x2 : A} → {y1 y2 : B} → (x1 ,, y1) ≡ (x2 ,, y2) → x1 ≡ x2
  firstEqualityOfPair {x1} {x2} {y1} {y2} refl = refl

  secondEqualityOfPair : {a b : _} {A : Set a} {B : Set b} → {x1 x2 : A} → {y1 y2 : B} → (x1 ,, y1) ≡ (x2 ,, y2) → y1 ≡ y2
  secondEqualityOfPair {x1} {x2} {y1} {y2} refl = refl

{-
  pairProductIsCountable : {a b : _} {A : Set a} {B : Set b} → (X : CountablyInfiniteSet A) → (Y : CountablyInfiniteSet B) → CountablyInfiniteSet (A && B)
  CountablyInfiniteSet.counting (pairProductIsCountable X Y) (a ,, b) = cantorPairing record { fst = CountablyInfiniteSet.counting X a ; snd = CountablyInfiniteSet.counting Y b }
  Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij (pairProductIsCountable {a} {b} {A} {B} X Y))) {(x1 ,, y1)} {(x2 ,, y2)} pr = ans x1=x2 y1=y2
    where
      p : (CountablyInfiniteSet.counting X x1 ,, CountablyInfiniteSet.counting Y y1) ≡ (CountablyInfiniteSet.counting X x2 ,, CountablyInfiniteSet.counting Y y2)
      p = Injection.property (Bijection.inj cantorBijection) pr
      p1 : CountablyInfiniteSet.counting X x1 ≡ CountablyInfiniteSet.counting X x2
      p1 = firstEqualityOfPair p
      p2 : CountablyInfiniteSet.counting Y y1 ≡ CountablyInfiniteSet.counting Y y2
      p2 = secondEqualityOfPair p
      x1=x2 : x1 ≡ x2
      x1=x2 = Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij X)) p1
      y1=y2 : y1 ≡ y2
      y1=y2 = Injection.property (Bijection.inj (CountablyInfiniteSet.countingIsBij Y)) p2
      ans : {a b : _} {A : Set a} {B : Set b} {x1 x2 : A} {y1 y2 : B} → (x1 ≡ x2) → (y1 ≡ y2) → (x1 ,, y1) ≡ (x2 ,, y2)
      ans x1=x2 y1=y2 rewrite x1=x2 | y1=y2 = refl
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairProductIsCountable X Y))) b with inspect (cantorInverse b)
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairProductIsCountable X Y))) b | (n1 ,, n2) with≡ blah with Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij X)) n1
  Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij (pairProductIsCountable X Y))) b | (n1 ,, n2) with≡ blah | b1 , pr1 with Surjection.property (Bijection.surj (CountablyInfiniteSet.countingIsBij Y)) n2
  ... | b2 , pr2 = (b1 ,, b2) , {!!}

-}

--  injectionToNMeansCountable : {a : _} {A : Set a} {f : A → ℕ} → Injection f → InfiniteSet A → Countable A
--  injectionToNMeansCountable {f = f} inj record { isInfinite = isInfinite } = {!!}
