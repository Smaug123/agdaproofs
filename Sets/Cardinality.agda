{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Semirings.Definition

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

{-
  triangle : (a : ℕ) → ℕ
  triangle zero = 0
  triangle (succ a) = succ a +N triangle a

  cantorPairing' : (a : ℕ) → (b : ℕ) → (s : ℕ) → (s ≡ a +N b) → ℕ
  cantorPairing' a b zero pr = 0
  cantorPairing' zero zero (succ s) ()
  cantorPairing' zero (succ b) (succ s) pr = succ (cantorPairing' 1 b (succ s) pr)
  cantorPairing' (succ a) zero (succ s) pr = succ (cantorPairing' 0 a s (succInjective (identityOfIndiscernablesRight _ _ _ _≡_ pr (applyEquality (λ i → succ i) (identityOfIndiscernablesLeft _ _ _ _≡_ (Semiring.commutative ℕSemiring a 0) refl)))))
  cantorPairing' (succ a) (succ b) (succ zero) pr = naughtE f
    where
      f : 0 ≡ succ b +N a
      f rewrite Semiring.commutative ℕSemiring (succ b) a = succInjective pr
  cantorPairing' (succ a) (succ b) (succ (succ s)) pr = succ (cantorPairing' (succ (succ a)) b (succ (succ s)) (identityOfIndiscernablesRight _ _ _ _≡_ pr (applyEquality succ (succExtracts a b))))

  cantorPairing'Zero : (x y s : ℕ) → (pr : s ≡ x +N y) → cantorPairing' x y s pr ≡ 0 → (x ≡ 0) && (y ≡ 0)
  cantorPairing'Zero x y zero pr pr' = sumZeroImpliesSummandsZero (equalityCommutative pr)
  cantorPairing'Zero zero zero (succ s) () pr'
  cantorPairing'Zero zero (succ y) (succ s) pr ()
  cantorPairing'Zero (succ x) zero (succ s) pr ()
  cantorPairing'Zero (succ x) (succ y) (succ zero) pr pr' = naughtE (identityOfIndiscernablesRight _ _ _ _≡_ (succInjective pr) (Semiring.commutative ℕSemiring x (succ y)))
  cantorPairing'Zero (succ x) (succ y) (succ (succ s)) pr ()

  cantorPairingInj' : (s1 s2 : ℕ) → (x1 x2 y1 y2 : ℕ) → (pr1 : s1 ≡ x1 +N y1) → (pr2 : s2 ≡ x2 +N y2) → (cantorPairing' x1 y1 s1 pr1) ≡ (cantorPairing' x2 y2 s2 pr2) → (x1 ≡ x2) && (y1 ≡ y2)
  cantorPairingInj' zero zero x1 x2 y1 y2 pr1 pr2 injF = transitivity (_&&_.fst x1y1) (equalityCommutative (_&&_.fst x2y2)) ,, transitivity (_&&_.snd x1y1) (equalityCommutative (_&&_.snd x2y2))
    where
      x2y2 : (x2 ≡ 0) && (y2 ≡ 0)
      x2y2 = sumZeroImpliesSummandsZero (equalityCommutative pr2)
      x1y1 : (x1 ≡ 0) && (y1 ≡ 0)
      x1y1 = sumZeroImpliesSummandsZero (equalityCommutative pr1)
  cantorPairingInj' zero (succ s2) x1 x2 y1 y2 pr1 pr2 injF = naughtE (equalityCommutative bad2)
    where
      x2y2 : (x2 ≡ 0) && (y2 ≡ 0)
      x2y2 = cantorPairing'Zero x2 y2 (succ s2) pr2 (equalityCommutative injF)
      bad : succ s2 ≡ y2
      bad = identityOfIndiscernablesRight _ _ _ _≡_ pr2 ((applyEquality (λ i → i +N y2) (_&&_.fst x2y2)))
      bad2 : succ s2 ≡ 0
      bad2 = transitivity bad (_&&_.snd x2y2)
  cantorPairingInj' (succ s1) zero x1 x2 y1 y2 pr1 pr2 injF = naughtE (equalityCommutative bad2)
    where
      x1y1 : (x1 ≡ 0) && (y1 ≡ 0)
      x1y1 = cantorPairing'Zero x1 y1 (succ s1) pr1 injF
      bad : succ s1 ≡ y1
      bad = identityOfIndiscernablesRight _ _ _ _≡_ pr1 ((applyEquality (λ i → i +N y1) (_&&_.fst x1y1)))
      bad2 : succ s1 ≡ 0
      bad2 = transitivity bad (_&&_.snd x1y1)
  cantorPairingInj' (succ s1) (succ s2) zero x2 zero y2 () pr2 injF
  cantorPairingInj' (succ s1) (succ s2) zero zero (succ .s1) zero refl () injF
  cantorPairingInj' (succ zero) (succ zero) zero zero (succ .0) (succ .0) refl refl injF = refl ,, refl
  cantorPairingInj' (succ zero) (succ (succ s2)) zero zero (succ .0) (succ .(succ s2)) refl refl injF = naughtE (equalityCommutative bad)
    where
      bad : 2 ≡ 0
      bad = _&&_.fst (cantorPairing'Zero 2 s2 (succ (succ s2)) refl (equalityCommutative (succInjective (succInjective injF))))
  cantorPairingInj' (succ (succ s1)) (succ zero) zero zero (succ .(succ s1)) (succ .0) refl refl injF = naughtE (equalityCommutative bad)
    where
      bad : 2 ≡ 0
      bad = _&&_.fst (cantorPairing'Zero 2 s1 (succ (succ s1)) refl (succInjective (succInjective injF)))
  cantorPairingInj' (succ (succ s1)) (succ (succ s2)) zero zero (succ .(succ s1)) (succ .(succ s2)) refl refl injF = refl ,, (applyEquality (λ i → succ (succ i)) rec')
    where
      rec : cantorPairing' 2 s1 (succ (succ s1)) refl ≡ cantorPairing' 2 s2 (succ (succ s2)) refl
      rec = succInjective (succInjective injF)
      rec' : (s1 ≡ s2)
      rec' = _&&_.snd (cantorPairingInj' (succ (succ s1)) (succ (succ s2)) 2 2 s1 s2 refl refl rec)
  cantorPairingInj' (succ s1) (succ s2) zero (succ x2) (succ .s1) zero refl pr2 injF = naughtE (equalityCommutative rec')
    where
      rec : cantorPairing' 1 s1 (succ s1) refl ≡ cantorPairing' 0 x2 s2 _
      rec = succInjective injF
      rec' : (1 ≡ zero)
      rec' = _&&_.fst (cantorPairingInj' (succ s1) s2 1 zero s1 x2 refl _ rec)
  cantorPairingInj' (succ s1) (succ zero) zero (succ x2) (succ .s1) (succ y2) refl pr2 injF = naughtE (identityOfIndiscernablesRight _ _ _ _≡_ (succInjective pr2) (Semiring.commutative ℕSemiring x2 (succ y2)))
  cantorPairingInj' (succ s1) (succ (succ s2)) zero (succ x2) (succ .s1) (succ y2) refl pr2 injF = naughtE (succInjective rec')
    where
      rec : cantorPairing' 1 s1 (succ s1) refl ≡ cantorPairing' (succ (succ x2)) y2 (succ (succ s2)) _
      rec = succInjective injF
      rec' : (1 ≡ succ (succ x2))
      rec' = _&&_.fst (cantorPairingInj' (succ s1) (succ (succ s2)) 1 (succ (succ x2)) s1 y2 refl _ rec)
  cantorPairingInj' (succ s1) (succ s2) (succ x1) zero y1 zero pr1 () injF
  cantorPairingInj' (succ s1) (succ s2) (succ zero) zero .s1 (succ .s2) refl refl injF = {!!}
  cantorPairingInj' (succ s1) (succ s2) (succ (succ x1)) zero zero (succ .s2) pr1 refl injF = {!!}
    where
      false : {!!}
      false = {!!}
  cantorPairingInj' (succ s1) (succ s2) (succ (succ x1)) zero (succ y1) (succ .s2) pr1 refl injF = {!!}
  cantorPairingInj' (succ s1) (succ s2) (succ x1) (succ x2) y1 y2 pr1 pr2 injF = {!!}

  cantorPairingInj : Injection cantorPairing
  Injection.property cantorPairingInj {zero ,, zero} {zero ,, zero} pr = refl
  Injection.property cantorPairingInj {zero ,, zero} {zero ,, succ snd} pr = exFalso {!!}
  Injection.property cantorPairingInj {zero ,, zero} {succ fst ,, snd} pr = {!!}
  Injection.property cantorPairingInj {zero ,, succ snd} {y} pr = {!!}
  Injection.property cantorPairingInj {succ fst ,, snd} {y} pr = {!!}

  cantorInverse : ℕ → (ℕ && ℕ)
  cantorInverse zero = (0 ,, 0)
  cantorInverse (succ z) = f (cantorInverse z)
    where
      f : (ℕ && ℕ) → (ℕ && ℕ)
      f (0 ,, s) = (succ s) ,, 0
      f (succ r ,, 0) = r ,, 1
      f (succ r ,, succ s) = (r ,, succ (succ s))

  cantorInvertible : Invertible cantorPairing
  Invertible.inverse cantorInvertible = cantorInverse
  Invertible.isLeft cantorInvertible zero = refl
  Invertible.isLeft cantorInvertible (succ b) with inspect (cantorInverse b)
  Invertible.isLeft cantorInvertible (succ b) | (zero ,, zero) with≡ x = {!!}
  Invertible.isLeft cantorInvertible (succ b) | (zero ,, succ snd) with≡ x = {!!}
  Invertible.isLeft cantorInvertible (succ b) | (succ fst ,, snd) with≡ x = {!!}
  Invertible.isRight cantorInvertible (a ,, b) = {!!}

  cantorBijection : Bijection cantorPairing
  cantorBijection = invertibleImpliesBijection cantorInvertible
  -}

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
