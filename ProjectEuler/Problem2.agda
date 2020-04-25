{-# OPTIONS --warning=error --safe --guardedness --without-K #-}

open import Sets.FinSet.Definition
open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Numbers.Naturals.EuclideanAlgorithm
open import Lists.Lists
open import Numbers.Primes.PrimeNumbers
open import Decidable.Relations
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Addition
open import Numbers.BinaryNaturals.Order
open import Sequences
open import Vectors
open import Orders.Total.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Partial.Sequences
open import Setoids.Orders.Total.Definition
open import Setoids.Setoids
open import Functions.Definition
open import Semirings.Definition

module ProjectEuler.Problem2 where

fibUnary : ℕ → ℕ
fibUnary zero = 1
fibUnary (succ zero) = 1
fibUnary (succ (succ n)) = fibUnary (succ n) +N fibUnary n

fibUnaryStrictlyPositive : (a : ℕ) → 0 <N fibUnary a
fibUnaryStrictlyPositive zero = le zero refl
fibUnaryStrictlyPositive (succ zero) = le zero refl
fibUnaryStrictlyPositive (succ (succ a)) = addStrongInequalities (fibUnaryStrictlyPositive (succ a)) (fibUnaryStrictlyPositive a)

fibUnaryIncreasing : (a : ℕ) → (fibUnary (succ a)) <N (fibUnary (succ (succ a)))
fibUnaryIncreasing zero = le zero refl
fibUnaryIncreasing (succ a) = identityOfIndiscernablesLeft _<N_ (additionPreservesInequalityOnLeft (fibUnary (succ a) +N fibUnary a) (fibUnaryStrictlyPositive (succ a))) (Semiring.sumZeroRight ℕSemiring (fibUnary (succ a) +N fibUnary a))

fibUnaryBiggerThanN : (a : ℕ) → (succ (succ (succ (succ a)))) <N fibUnary (succ (succ (succ (succ a))))
fibUnaryBiggerThanN zero = le zero refl
fibUnaryBiggerThanN (succ a) = TotalOrder.<Transitive ℕTotalOrder (succPreservesInequality (fibUnaryBiggerThanN a)) (ans ((fibUnary (succ a) +N fibUnary a) +N fibUnary (succ a)) ans')
  where
    ans : {t : ℕ} → (u : ℕ) → 1 <N u → succ t <N t +N u
    ans {t} u (le x proof) rewrite Semiring.commutative ℕSemiring x 1 = le x (transitivity (applyEquality succ (Semiring.commutative ℕSemiring x (succ t))) (transitivity (applyEquality (λ i → succ (succ i)) (Semiring.commutative ℕSemiring t x)) (transitivity (applyEquality (_+N t) proof) (Semiring.commutative ℕSemiring u t))))
    ans' : 1 <N (fibUnary (succ a) +N fibUnary a) +N fibUnary (succ a)
    ans' with fibUnaryStrictlyPositive (succ a)
    ... | fibPos with fibUnary (succ a)
    ans' | fibPos | succ bl rewrite Semiring.commutative ℕSemiring (bl +N fibUnary a) (succ bl) = succPreservesInequality (le (bl +N (bl +N fibUnary a)) (Semiring.sumZeroRight ℕSemiring _))

fibUnaryArchimedean : (a : ℕ) → Sg ℕ (λ i → a <N fibUnary i)
fibUnaryArchimedean zero = 0 , le zero refl
fibUnaryArchimedean (succ zero) = 2 , le zero refl
fibUnaryArchimedean (succ (succ zero)) = 3 , le zero refl
fibUnaryArchimedean (succ (succ (succ zero))) = 4 , le 1 refl
fibUnaryArchimedean (succ (succ (succ (succ a)))) = (succ (succ (succ (succ a)))) , fibUnaryBiggerThanN a

everyThird : {a : _} {A : Set a} → Sequence A → Sequence A
Sequence.head (everyThird S) = Sequence.head (tailFrom 2 S)
Sequence.tail (everyThird S) = everyThird (tailFrom 3 S)

record FibEntry : Set where
  field
    prev : BinNat
    curr : BinNat

nextFib : FibEntry → FibEntry
nextFib record { prev = prev ; curr = curr } = record { prev = curr ; curr = prev +B curr }

fib : Sequence BinNat
fib = Sequences.map FibEntry.curr (unfold nextFib record { prev = NToBinNat 0 ; curr = NToBinNat 1 })

fibMove : (n : ℕ) → FibEntry.prev (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) (succ n)) ≡ FibEntry.curr (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) n)
fibMove zero = refl
fibMove (succ n) rewrite indexAndUnfold nextFib (record { prev = [] ; curr = one :: [] }) (succ n) = refl

fibAlternative : (N : ℕ) → index fib N ≡ FibEntry.curr (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) N)
fibAlternative n rewrite equalityCommutative (mapAndIndex (unfold nextFib record { prev = NToBinNat 0 ; curr = NToBinNat 1 }) FibEntry.curr n) = refl

fibAlternative' : (n : ℕ) → FibEntry.curr (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) (succ n)) ≡ FibEntry.prev (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) n) +B FibEntry.curr (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) n)
fibAlternative' zero = refl
fibAlternative' (succ n) rewrite indexAndUnfold nextFib (record { prev = [] ; curr = one :: [] }) (succ n) = refl

fibsCanonical : (n : ℕ) → canonical (index fib n) ≡ index fib n
fibsCanonical zero = refl
fibsCanonical (succ zero) = refl
fibsCanonical (succ (succ n)) = transitivity (applyEquality canonical {index fib (succ (succ n))} {FibEntry.prev (index (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) n) +B FibEntry.curr (index (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) n)} (transitivity (fibAlternative (succ (succ n))) (fibAlternative' (succ n)))) (transitivity (sumCanonical (FibEntry.prev (index (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) n)) (FibEntry.curr (index (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) n)) (transitivity (transitivity (applyEquality canonical (fibMove n)) (transitivity (applyEquality canonical (equalityCommutative (fibAlternative n))) (transitivity (fibsCanonical n) (fibAlternative n)))) (equalityCommutative (fibMove n))) (transitivity (applyEquality canonical (mapAndIndex (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) FibEntry.curr n)) (transitivity (fibsCanonical (succ n)) (equalityCommutative (mapAndIndex (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) FibEntry.curr n))))) (equalityCommutative (transitivity (fibAlternative (succ (succ n))) (fibAlternative' (succ n)))))

fibStart : take 5 fib ≡ vecMap NToBinNat (1 ,- 1 ,- 2 ,- 3 ,- 5 ,- [])
fibStart = refl

fibsMatch : (n : ℕ) → binNatToN (index fib n) ≡ fibUnary n
fibsMatch zero = refl
fibsMatch (succ zero) = refl
fibsMatch (succ (succ n)) rewrite equalityCommutative (fibsMatch (succ n)) | equalityCommutative (fibsMatch n) | equalityCommutative (mapAndIndex (unfold nextFib record { prev = NToBinNat 0 ; curr = NToBinNat 1 }) FibEntry.curr (succ (succ n))) | indexAndUnfold nextFib (record { prev = [] ; curr = one :: [] }) (succ n) | equalityCommutative (mapAndIndex (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) FibEntry.curr n) | equalityCommutative (mapAndIndex (unfold nextFib (record { prev = [] ; curr = one :: [] })) FibEntry.curr n) | indexAndUnfold nextFib (nextFib (record { prev = [] ; curr = one :: [] })) n | indexAndUnfold nextFib (record { prev = [] ; curr = one :: [] }) n = ans
  where
    x = FibEntry.curr (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) n)
    y = FibEntry.prev (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) n)
    ans : binNatToN (x +B (y +B x)) ≡ binNatToN (y +B x) +N binNatToN x
    ans rewrite +BCommutative x (y +B x) = +BIsHom (y +B x) x

fibsMatch' : (n : ℕ) → NToBinNat (fibUnary n) ≡ index fib n
fibsMatch' n = transitivity (applyEquality NToBinNat (equalityCommutative (fibsMatch n))) (transitivity (binToBin (index fib n)) (fibsCanonical n))

ArchimedeanSequence : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} (pOrder : SetoidPartialOrder S _<_) (S : Sequence A) → Set (a ⊔ c)
ArchimedeanSequence {A = A} {_<_ = _<_} _ S = (x : A) → Sg ℕ (λ n → x < (index S n))

archimImpliesTailArchim : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} (pOrder : SetoidPartialOrder S _<_) {S : Sequence A} → ArchimedeanSequence pOrder S → (Sg ℕ (λ i → index S 0 < index S i)) → ArchimedeanSequence pOrder (Sequence.tail S)
archimImpliesTailArchim {S} pOrder arch 0small x with arch x
archimImpliesTailArchim pOrder {S} arch (zero , S0<SN) x | zero , pr = exFalso (SetoidPartialOrder.irreflexive pOrder S0<SN)
archimImpliesTailArchim pOrder {S} arch (succ N , S0<SN) x | zero , pr = N , SetoidPartialOrder.<Transitive pOrder pr S0<SN
archimImpliesTailArchim pOrder arch 0small x | succ N , pr = N , pr

takeUpTo : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} {pOrder : SetoidPartialOrder S _<_} {seq : Sequence A} → (arch : ArchimedeanSequence pOrder seq) → (lim : A) → List A
takeUpTo {seq = S} arch lim with arch lim
takeUpTo {seq = S} arch lim | zero , pr = []
takeUpTo {seq = S} arch lim | succ N , pr = vecToList (take N S)

archim : ArchimedeanSequence (partialOrderToSetoidPartialOrder BinNatOrder) fib
archim x with fibUnaryArchimedean (binNatToN x)
archim x | N , pr = N , u
  where
    t : (canonical x) <B (NToBinNat (binNatToN (index (Sequences.map FibEntry.curr (unfold nextFib (record { prev = [] ; curr = one :: [] }))) N)))
    t rewrite (fibsMatch N) = identityOfIndiscernablesLeft _<B_ (translate' _ _ pr) (binToBin x)
    u : x <B (index (Sequences.map FibEntry.curr (unfold nextFib (record { prev = [] ; curr = one :: [] }))) N)
    u rewrite equalityCommutative (mapAndIndex (unfold nextFib (record { prev = [] ; curr = one :: [] })) FibEntry.curr N) with transitivity (canonicalFirst x (NToBinNat (fibUnary N)) Equal) (identityOfIndiscernablesLeft _<B_ (translate' (binNatToN x) (fibUnary N) pr) (binToBin x))
    ... | r = identityOfIndiscernablesRight {a = x} {b = NToBinNat (fibUnary N)} {c = FibEntry.curr (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) N)} _<B_ r (transitivity (fibsMatch' N) (fibAlternative N))

isEven : BinNat → Set
isEven [] = True
isEven (zero :: xs) = True
isEven (one :: xs) = False

isEvenAgrees : (n : BinNat) → isEven n → 2 ∣ (binNatToN n)
isEvenAgrees [] nEven = divides (record { quot = zero ; rem = zero ; pr = refl ; remIsSmall = inl (le 1 refl) ; quotSmall = inl (le 1 refl)}) refl
isEvenAgrees (zero :: n) nEven = divides (record { quot = binNatToN n ; rem = zero ; pr = Semiring.sumZeroRight ℕSemiring _ ; remIsSmall = inl (le 1 refl) ; quotSmall = inl (le 1 refl) }) refl

isEvenIncrs : (n : BinNat) → isEven n → isEven (incr (incr n))
isEvenIncrs [] nEven = record {}
isEvenIncrs (zero :: n) nEven = record {}

isEvenAgrees' : (n : ℕ) → 2 ∣ n → isEven (NToBinNat n)
isEvenAgrees' zero nEven = record {}
isEvenAgrees' (succ zero) (divides record { quot = (succ zero) ; rem = zero ; pr = () ; remIsSmall = remIsSmall ; quotSmall = (inl x) } refl)
isEvenAgrees' (succ zero) (divides record { quot = (succ (succ quot)) ; rem = zero ; pr = () ; remIsSmall = remIsSmall ; quotSmall = (inl x) } refl)
isEvenAgrees' (succ (succ n)) (divides record { quot = succ quot ; rem = zero ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = inl 0<2 } refl) with isEvenAgrees' n (divides record { quot = quot ; rem = zero ; pr = transitivity (transitivity (Semiring.sumZeroRight ℕSemiring _) (Semiring.commutative ℕSemiring quot (quot +N 0))) (succInjective (succInjective (transitivity (equalityCommutative (applyEquality succ (transitivity (Semiring.sumZeroRight ℕSemiring (quot +N succ (quot +N zero))) (Semiring.commutative ℕSemiring quot (succ (quot +N 0)))))) pr))) ; remIsSmall = remIsSmall ; quotSmall = inl 0<2 } refl)
... | bl = isEvenIncrs (NToBinNat n) bl

isEvenWellDefined : (n m : BinNat) → canonical n ≡ canonical m → isEven n → isEven m
isEvenWellDefined [] [] n=m nEven = record {}
isEvenWellDefined [] (zero :: m) n=m nEven = record {}
isEvenWellDefined (zero :: n) [] n=m nEven = record {}
isEvenWellDefined (zero :: n) (zero :: m) n=m nEven = record {}
isEvenWellDefined (zero :: n) (one :: m) n=m nEven with canonical n
isEvenWellDefined (zero :: n) (one :: m) () nEven | []
isEvenWellDefined (zero :: n) (one :: m) () nEven | x :: bl

isEvenDecidable : DecidableRelation isEven
isEvenDecidable [] = inl (record {})
isEvenDecidable (zero :: x₁) = inl (record {})
isEvenDecidable (one :: x₁) = inr (λ x → x)

increasing : StrictlyIncreasing (partialOrderToSetoidPartialOrder BinNatOrder) (Sequence.tail fib)
increasing m = SetoidPartialOrder.<WellDefined (partialOrderToSetoidPartialOrder BinNatOrder) (fibsMatch' (succ m)) (fibsMatch' (succ (succ m))) (translate' (fibUnary (succ m)) (fibUnary (succ (succ m))) (fibUnaryIncreasing m))

private
  increasingNaturalsBoundLemma : (S : Sequence ℕ) → .(StrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S) → (fuel : ℕ) → (bound : ℕ) → List ℕ
  increasingNaturalsBoundLemma s incr zero n with TotalOrder.totality ℕTotalOrder (Sequence.head s) n
  ... | inl (inl x) = n :: []
  ... | inl (inr x) = []
  ... | inr x = n :: []
  increasingNaturalsBoundLemma s incr (succ fuel) n with TotalOrder.totality ℕTotalOrder (Sequence.head s) n
  ... | inl (inl x) = n :: increasingNaturalsBoundLemma (Sequence.tail s) (tailRespectsStrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) s incr) fuel n
  ... | inl (inr x) = []
  ... | inr x = n :: []

increasingNaturalsBound : (S : Sequence ℕ) → .(StrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S) → (bound : ℕ) → List ℕ
increasingNaturalsBound S incr n = increasingNaturalsBoundLemma S incr (succ n) n

boundedInIncreasingLemma : (S : Sequence ℕ) → (incr : StrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S) → (bound fuel : ℕ) → (i : ℕ) → (index S i ≤N bound) → .(i <N fuel) → contains (increasingNaturalsBoundLemma S incr fuel bound) (index S i)
boundedInIncreasingLemma S incr bound zero i Si<b ()
boundedInIncreasingLemma S incr bound (succ fuel) zero Si<b i<fu with TotalOrder.totality ℕTotalOrder (Sequence.head S) bound
... | inl (inl x) = {!inr ?!}
boundedInIncreasingLemma S incr bound (succ fuel) zero (inl y) i<fu | inl (inr x) = exFalso (lessIrreflexive (lessTransitive x y))
boundedInIncreasingLemma S incr bound (succ fuel) zero (inr y) i<fu | inl (inr x) = exFalso (lessIrreflexive (identityOfIndiscernablesRight _<N_ x y))
... | inr x = inl (equalityCommutative x)
boundedInIncreasingLemma S incr bound (succ fuel) (succ i) Si<b i<fu with TotalOrder.totality ℕTotalOrder (Sequence.head S) bound
boundedInIncreasingLemma S incr bound (succ fuel) (succ i) (inl proceed) i<fu | inl (inl x) = inr (boundedInIncreasingLemma (Sequence.tail S) (tailRespectsStrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S incr) bound fuel i (inl proceed) (canRemoveSuccFrom<N i<fu))
boundedInIncreasingLemma S incr bound (succ fuel) (succ i) (inr found) i<fu | inl (inl x) = inl (equalityCommutative found)
boundedInIncreasingLemma S incr bound (succ fuel) (succ i) (inl bad) i<fu | inl (inr x) with strictlyIncreasingImplies' (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) _ incr 0 (succ i) (succIsPositive i)
... | r = exFalso (lessIrreflexive (lessTransitive x (lessTransitive r bad)))
boundedInIncreasingLemma S incr bound (succ fuel) (succ i) (inr bad) i<fu | inl (inr x) with strictlyIncreasingImplies' (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) _ incr 0 (succ i) (succIsPositive i)
... | r = exFalso (lessIrreflexive (lessTransitive x (identityOfIndiscernablesRight _<N_ r bad)))
boundedInIncreasingLemma S incr bound (succ fuel) (succ i) (inl t<b) i<fu | inr h=b with strictlyIncreasingImplies' (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) _ incr 0 (succ i) (succIsPositive i)
... | r rewrite h=b = exFalso (lessIrreflexive (lessTransitive r t<b))
boundedInIncreasingLemma S incr bound (succ fuel) (succ i) (inr b=t) i<fu | inr h=b with strictlyIncreasingImplies' (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) _ incr 0 (succ i) (succIsPositive i)
... | r rewrite h=b = exFalso (lessIrreflexive (identityOfIndiscernablesRight _<N_ r b=t))

boundedInIncreasing : (S : Sequence ℕ) → (incr : StrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S) → (bound : ℕ) → (i : ℕ) → (index S i ≤N bound) → contains (increasingNaturalsBound S incr bound) (index S i)
boundedInIncreasing S incr bound i = {!!}

increasingNaturalsBoundBoundedLemma : (S : Sequence ℕ) → (incr : StrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S) → (bound fuel : ℕ) → Lists.Lists.allTrue (λ n → n ≤N bound) (increasingNaturalsBoundLemma S incr fuel bound)
increasingNaturalsBoundBoundedLemma S incr bound zero with TotalOrder.totality ℕTotalOrder (Sequence.head S) bound
... | inl (inl x) = inr refl ,, record {}
... | inl (inr x) = record {}
... | inr x = inr refl ,, record {}
increasingNaturalsBoundBoundedLemma S incr bound (succ fuel) with TotalOrder.totality ℕTotalOrder (Sequence.head S) bound
... | inl (inl x) = inr refl ,, increasingNaturalsBoundBoundedLemma (Sequence.tail S) (tailRespectsStrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S incr) bound fuel
... | inl (inr x) = record {}
... | inr x = inr refl ,, record {}

increasingNaturalsBoundBounded : (S : Sequence ℕ) → (incr : StrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) S) → (bound : ℕ) → Lists.Lists.allTrue (λ n → n ≤N bound) (increasingNaturalsBound S incr bound)
increasingNaturalsBoundBounded S incr bound = increasingNaturalsBoundBoundedLemma S incr bound (succ bound)

private
  increasingBoundLemma : {a b : _} {A : Set a} {_<_ : A → A → Set b} (S : Sequence A) → {f : A → ℕ} → .(op : (x y : A) → x < y → (f x) <N (f y)) → .(StrictlyIncreasing (partialOrderToSetoidPartialOrder (TotalOrder.order ℕTotalOrder)) (Sequences.map f S)) → (fuel : ℕ) → (bound : A) → List A
  increasingBoundLemma s incr fuel bound = {!!}

{-
fibsLessThan4Mil : List BinNat
fibsLessThan4Mil = takeUpToMonotone {tOrder = BinNatTOrder} (archimImpliesTailArchim {tOrder = BinNatTOrder} archim (2 , ordersAgree 1 2 (le zero refl))) increasing (one :: one :: one :: one :: zero :: one :: zero :: zero :: zero :: zero :: one :: zero :: zero :: one :: zero :: zero :: zero :: zero :: zero :: zero :: zero :: one :: [])

evens : List BinNat
evens = filter' isEvenDecidable fibsLessThan4Mil

ans : BinNat
ans = fold _+B_ [] evens

-}
