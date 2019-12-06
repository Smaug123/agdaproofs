{-# OPTIONS --warning=error --safe --guardedness #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Lists.Lists
open import Numbers.Primes.PrimeNumbers
open import Decidable.Relations
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Addition
open import Numbers.BinaryNaturals.Order
open import Sequences
open import Vectors
open import Orders
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
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

record FibEntry : Set where
  field
    prev : BinNat
    curr : BinNat

nextFib : FibEntry → FibEntry
nextFib record { prev = prev ; curr = curr } = record { prev = curr ; curr = prev +B curr }

fib : Sequence BinNat
fib = Sequences.map FibEntry.curr (unfold nextFib record { prev = NToBinNat 0 ; curr = NToBinNat 1 })

fibStart : take fib 5 ≡ vecMap NToBinNat (1 ,- 1 ,- 2 ,- 3 ,- 5 ,- [])
fibStart = refl

fibsMatch : (n : ℕ) → binNatToN (index fib n) ≡ fibUnary n
fibsMatch zero = refl
fibsMatch (succ zero) = refl
fibsMatch (succ (succ n)) rewrite equalityCommutative (fibsMatch n) | equalityCommutative (fibsMatch (succ n)) | equalityCommutative (mapAndIndex (unfold nextFib record { prev = NToBinNat 0 ; curr = NToBinNat 1 }) FibEntry.curr (succ (succ n))) | indexAndUnfold nextFib (record { prev = [] ; curr = one :: [] }) (succ n) | equalityCommutative (mapAndIndex (unfold nextFib (nextFib (record { prev = [] ; curr = one :: [] }))) FibEntry.curr n) | equalityCommutative (mapAndIndex (unfold nextFib (record { prev = [] ; curr = one :: [] })) FibEntry.curr n) | indexAndUnfold nextFib (nextFib (record { prev = [] ; curr = one :: [] })) n | indexAndUnfold nextFib (record { prev = [] ; curr = one :: [] }) n = ans
  where
    x = FibEntry.curr (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) n)
    y = FibEntry.prev (index (unfold nextFib (record { prev = [] ; curr = one :: [] })) n)
    ans : binNatToN (x +B (y +B x)) ≡ binNatToN (y +B x) +N binNatToN x
    ans rewrite +BCommutative x (y +B x) = +BIsHom (y +B x) x

IncreasingSequence : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} {pOrder : SetoidPartialOrder S _<_} (tOrder : SetoidTotalOrder pOrder) (S : Sequence A) → Set c
IncreasingSequence {_<_ = _<_} tOrder s = (n : ℕ) → (index s n) < (index s (succ n))

ArchimedeanSequence : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} {pOrder : SetoidPartialOrder S _<_} (tOrder : SetoidTotalOrder pOrder) (S : Sequence A) → Set (a ⊔ c)
ArchimedeanSequence {A = A} {_<_ = _<_} tOrder S = (x : A) → Sg ℕ (λ n → x < (index S n))

archimImpliesTailArchim : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} {S : Sequence A} → ArchimedeanSequence tOrder S → (Sg ℕ (λ i → index S 0 < index S i)) → ArchimedeanSequence tOrder (Sequence.tail S)
archimImpliesTailArchim {tOrder = tOrder} {S} arch 0small x with arch x
archimImpliesTailArchim {pOrder = pOrder} {tOrder = tOrder} {S} arch (zero , S0<SN) x | zero , pr = exFalso (SetoidPartialOrder.irreflexive pOrder S0<SN)
archimImpliesTailArchim {pOrder = pOrder} {tOrder = tOrder} {S} arch (succ N , S0<SN) x | zero , pr = N , SetoidPartialOrder.<Transitive pOrder pr S0<SN
archimImpliesTailArchim {tOrder = tOrder} {S} arch 0small x | succ N , pr = N , pr

takeUpTo : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} {seq : Sequence A} → (arch : ArchimedeanSequence tOrder seq) → (lim : A) → List A
takeUpTo {seq = S} arch lim with arch lim
takeUpTo {seq = S} arch lim | zero , pr = []
takeUpTo {seq = S} arch lim | succ N , pr = vecToList (take S N)

takeUpToMonotone : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} {seq : Sequence A} → (arch : ArchimedeanSequence tOrder seq) → (incr : IncreasingSequence tOrder seq) → (lim : A) → List A
takeUpToMonotone {tOrder = tOrder} {seq = S} arch increasing lim with Sequence.head S
... | head with SetoidTotalOrder.totality tOrder head lim
takeUpToMonotone {tOrder = tOrder} {S} arch increasing lim | head | inl (inl head<lim) = head :: {!takeUpToMonotone {tOrder = tOrder} {seq = S} arch increasing lim!}
takeUpToMonotone {tOrder = tOrder} {S} arch increasing lim | head | inl (inr lim<head) = []
takeUpToMonotone {tOrder = tOrder} {S} arch increasing lim | head | inr head=lim = {!!}

increasing : IncreasingSequence BinNatTOrder (Sequence.tail fib)
increasing n with ordersAgree (fibUnary (succ n)) (fibUnary (succ (succ n))) (fibUnaryIncreasing n)
... | bl rewrite fibsMatch n | fibsMatch (succ n) = {!!}

archim : ArchimedeanSequence BinNatTOrder fib
archim x with fibUnaryArchimedean (binNatToN x)
archim x | N , pr = N , u
  where
    t : PartialOrder._<_ BinNatOrder (canonical x) (NToBinNat (binNatToN (index (Sequences.map FibEntry.curr (unfold nextFib (record { prev = [] ; curr = one :: [] }))) N)))
    t rewrite (fibsMatch N) = identityOfIndiscernablesLeft (PartialOrder._<_ BinNatOrder) (ordersAgree (binNatToN x) (fibUnary N) pr) (binToBin x)
    u : PartialOrder._<_ BinNatOrder x (index (Sequences.map FibEntry.curr (unfold nextFib (record { prev = [] ; curr = one :: [] }))) N)
    u = SetoidPartialOrder.<WellDefined BinNatPOrder {canonical x} {x} (equalityCommutative (canonicalIdempotent x)) (transitivity (applyEquality canonical (binToBin (index (Sequences.map FibEntry.curr (unfold nextFib (record { prev = [] ; curr = one :: [] }))) N))) (equalityCommutative (canonicalIdempotent (index (Sequences.map FibEntry.curr (unfold nextFib (record { prev = [] ; curr = one :: [] }))) N)))) t

fibsLessThan4Mil : List BinNat
fibsLessThan4Mil = takeUpToMonotone {tOrder = BinNatTOrder} (archimImpliesTailArchim {tOrder = BinNatTOrder} archim (2 , ordersAgree 1 2 (le zero refl))) increasing (one :: one :: one :: one :: zero :: one :: zero :: zero :: zero :: zero :: one :: zero :: zero :: one :: zero :: zero :: zero :: zero :: zero :: zero :: zero :: one :: [])

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

evens : List BinNat
evens = filter' isEvenDecidable fibsLessThan4Mil

ans : BinNat
ans = fold _+B_ [] evens
