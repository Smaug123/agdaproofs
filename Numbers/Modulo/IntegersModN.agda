{-# OPTIONS --safe --warning=error #-}
-- These are explicitly with-K, because we currently encode an element of Zn as
-- a natural together with a proof that it is small.

open import LogicalFormulae
open import Groups.Definition
open import Groups.Groups
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Addition -- TODO remove this dependency
open import Numbers.Primes.PrimeNumbers
open import Setoids.Setoids
open import Sets.FinSet
open import Sets.FinSetWithK
open import Functions
open import Numbers.Naturals.WithK
open import Semirings.Definition
open import Orders

module Numbers.Modulo.IntegersModN where
  record ℤn (n : ℕ) (pr : 0 <N n) : Set where
    field
      x : ℕ
      xLess : x <N n

  equalityZn : {n : ℕ} {pr : 0 <N n} → (a b : ℤn n pr) → (ℤn.x a ≡ ℤn.x b) → a ≡ b
  equalityZn record { x = a ; xLess = aLess } record { x = .a ; xLess = bLess } refl rewrite <NRefl aLess bLess = refl

  cancelSumFromInequality : {a b c : ℕ} → a +N b <N a +N c → b <N c
  cancelSumFromInequality {a} {b} {c} (le x proof) = le x help
    where
      help : succ x +N b ≡ c
      help rewrite Semiring.+Associative ℕSemiring (succ x) a b | Semiring.commutative ℕSemiring x a | equalityCommutative (Semiring.+Associative ℕSemiring (succ a) x b) | Semiring.commutative ℕSemiring a (x +N b) | Semiring.commutative ℕSemiring (succ (x +N b)) a = canSubtractFromEqualityLeft {a} proof

  _+n_ : {n : ℕ} {pr : 0 <N n} → ℤn n pr → ℤn n pr → ℤn n pr
  _+n_ {0} {le x ()} a b
  _+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } with orderIsTotal (a +N b) (succ n)
  _+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl (a+b<n)) = record { x = a +N b ; xLess = a+b<n }
  _+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr (n<a+b)) = record { x = subtractionNResult.result sub ; xLess = pr2 }
      where
        sub : subtractionNResult (succ n) (a +N b) (inl n<a+b)
        sub = -N (inl n<a+b)
        pr1 : a +N b <N succ n +N succ n
        pr1 = addStrongInequalities aLess bLess
        pr1' : succ n +N (subtractionNResult.result sub) <N succ n +N succ n
        pr1' rewrite subtractionNResult.pr sub = pr1
        pr2 : subtractionNResult.result sub <N succ n
        pr2 = cancelSumFromInequality pr1'
  _+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr (a+b=n) = record { x = 0 ; xLess = succIsPositive n }

  plusZnIdentityRight : {n : ℕ} → {pr : 0 <N n} → (a : ℤn n pr) → (a +n record { x = 0 ; xLess = pr }) ≡ a
  plusZnIdentityRight {zero} {()} a
  plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } with orderIsTotal (a +N 0) (succ x)
  plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } | inl (inl a<sx) = equalityZn _ _ (Semiring.commutative ℕSemiring a 0)
  plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } | inl (inr sx<a) = exFalso (f aLess sx<a)
    where
      f : (aL : a <N succ x) → (sx<a : succ x <N a +N 0) → False
      f aL sx<a rewrite Semiring.commutative ℕSemiring a 0 = orderIsIrreflexive aL sx<a
  plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } | inr a=sx = exFalso (f aLess a=sx)
    where
      f : (aL : a <N succ x) → (a=sx : a +N 0 ≡ succ x) → False
      f aL a=sx rewrite Semiring.commutative ℕSemiring a 0 | a=sx = TotalOrder.irreflexive ℕTotalOrder aL


  plusZnIdentityLeft : {n : ℕ} → {pr : 0 <N n} → (a : ℤn n pr) → (record { x = 0 ; xLess = pr }) +n a ≡ a
  plusZnIdentityLeft {zero} {()}
  plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } with orderIsTotal x (succ n)
  plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } | inl (inl x<succn) rewrite <NRefl x<succn xLess = refl
  plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } | inl (inr succn<x) = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.transitive ℕTotalOrder succn<x xLess))
  plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } | inr x=succn rewrite x=succn = exFalso (TotalOrder.irreflexive ℕTotalOrder xLess)

  subLemma : {a b c : ℕ} → (pr1 : a <N b) → (pr2 : a <N c) → (pr : b ≡ c) → (subtractionNResult.result (-N (inl pr1))) ≡ (subtractionNResult.result (-N (inl pr2)))
  subLemma {a} {b} {c} a<b a<c b=c rewrite b=c | <NRefl a<b a<c = refl

  plusZnCommutative : {n : ℕ} → {pr : 0 <N n} → (a b : ℤn n pr) → (a +n b) ≡ b +n a
  plusZnCommutative {zero} {()} a b
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } with orderIsTotal (a +N b) (succ n)
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) with orderIsTotal (b +N a) (succ n)
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) | inl (inl b+a<sn) = equalityZn _ _ (Semiring.commutative ℕSemiring a b)
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) | inl (inr sn<b+a) = exFalso (f a+b<sn sn<b+a)
    where
      f : (a +N b) <N succ n → succ n <N b +N a → False
      f pr1 pr2 rewrite Semiring.commutative ℕSemiring b a = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr2 pr1)
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) | inr b+a=sn = exFalso (f a+b<sn b+a=sn)
    where
      f : (a +N b) <N succ n → b +N a ≡ succ n → False
      f pr1 eq rewrite Semiring.commutative ℕSemiring b a | eq = TotalOrder.irreflexive ℕTotalOrder pr1
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) with orderIsTotal (b +N a) (succ n)
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) | inl (inl b+a<sn) = exFalso (f sn<a+b b+a<sn)
    where
      f : succ n <N a +N b → b +N a <N succ n → False
      f pr1 pr2 rewrite Semiring.commutative ℕSemiring b a = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive sn<a+b b+a<sn)
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) | inl (inr sn<b+a) = equalityZn _ _ (subLemma sn<a+b sn<b+a (Semiring.commutative ℕSemiring a b))
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) | inr sn=b+a = exFalso (f sn<a+b sn=b+a)
    where
      f : succ n <N a +N b → b +N a ≡ succ n → False
      f pr eq rewrite Semiring.commutative ℕSemiring b a | eq = TotalOrder.irreflexive ℕTotalOrder pr
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b with orderIsTotal (b +N a) (succ n)
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b | inl (inl b+a<sn) = exFalso f
    where
      f : False
      f rewrite Semiring.commutative ℕSemiring b a | sn=a+b = TotalOrder.irreflexive ℕTotalOrder b+a<sn
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b | inl (inr sn<b+a) = exFalso f
    where
      f : False
      f rewrite Semiring.commutative ℕSemiring b a | sn=a+b = TotalOrder.irreflexive ℕTotalOrder sn<b+a
  plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b | inr sn=b+a = equalityZn _ _ refl

  help30 : {a b c n : ℕ} → (c <N n) → (a +N b ≡ n) → (n<b+c : n <N b +N c) → (n <N a +N subtractionNResult.result (-N (inl n<b+c))) → False
  help30 {a} {b} {c} {n} c<n a+b=n n<b+c x = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr5 c<n)
    where
      pr : n +N n <N a +N (subtractionNResult.result (-N (inl n<b+c)) +N n)
      pr = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequality n x) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      pr2 : n +N n <N a +N (b +N c)
      pr2 = identityOfIndiscernablesRight _ _ _ _<N_ pr (applyEquality (a +N_) (addMinus (inl n<b+c)))
      pr3 : n +N n <N (a +N b) +N c
      pr3 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = pr2
      pr4 : n +N n <N c +N n
      pr4 rewrite Semiring.commutative ℕSemiring c n = identityOfIndiscernablesRight _ _ _ _<N_ pr3 (applyEquality (_+N c) a+b=n)
      pr5 : n <N c
      pr5 = subtractionPreservesInequality n pr4

  help31 : {a b c n : ℕ} → (a +N b ≡ n) → (n<b+c : n <N b +N c) → (a +N subtractionNResult.result (-N (inl n<b+c))) ≡ c
  help31 {a} {b} {c} {n} a+b=n n<b+c = canSubtractFromEqualityLeft pr2
    where
      pr1 : a +N (n +N subtractionNResult.result (-N (inl n<b+c))) ≡ n +N c
      pr1 rewrite addMinus' (inl n<b+c) | Semiring.+Associative ℕSemiring a b c | a+b=n = refl
      pr2 : n +N (a +N subtractionNResult.result (-N (inl n<b+c))) ≡ n +N c
      pr2 = identityOfIndiscernablesLeft _ _ _ _≡_ pr1 (lemm a n (subtractionNResult.result (-N (inl n<b+c))))
        where
          lemm : (a b c : ℕ) → a +N (b +N c) ≡ b +N (a +N c)
          lemm a b c rewrite Semiring.+Associative ℕSemiring a b c | Semiring.commutative ℕSemiring a b | equalityCommutative (Semiring.+Associative ℕSemiring b a c) = refl

  help7 : {a b c n : ℕ} → b +N c ≡ n → a <N n → (n<a+b : n <N a +N b) → (subtractionNResult.result (-N (inl n<a+b)) +N c ≡ n) → False
  help7 {a} {b} {c} {n} b+c=n a<n n<a+b x = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _ _ _ _<N_ a<n pr5)
    where
      pr : (n +N subtractionNResult.result (-N (inl n<a+b))) +N c ≡ n +N n
      pr = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (n +N_) x) (Semiring.+Associative ℕSemiring n _ c)
      pr2 : (a +N b) +N c ≡ n +N n
      pr2 = identityOfIndiscernablesLeft _ _ _ _≡_ pr (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      pr3 : a +N (b +N c) ≡ n +N n
      pr3 rewrite Semiring.+Associative ℕSemiring a b c = pr2
      pr4 : a +N n ≡ n +N n
      pr4 = identityOfIndiscernablesLeft _ _ _ _≡_ pr3 (applyEquality (a +N_) b+c=n)
      pr5 : a ≡ n
      pr5 = canSubtractFromEqualityRight pr4

  help29 : {a b c n : ℕ} → (c <N n) → (n<b+c : n <N b +N c) → (a +N subtractionNResult.result (-N (inl n<b+c))) ≡ n → a +N b ≡ n → False
  help29 {a} {b} {c} {n} c<n n<b+c pr a+b=n = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _ _ _ _<N_ c<n p4)
    where
      p1 : a +N (subtractionNResult.result (-N (inl n<b+c)) +N n) ≡ n +N n
      p1 = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (_+N n) pr) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      p2 : (a +N b) +N c ≡ n +N n
      p2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = identityOfIndiscernablesLeft _ _ _ _≡_ p1 (applyEquality (a +N_) (addMinus (inl n<b+c)))
      p3 : n +N c ≡ n +N n
      p3 = identityOfIndiscernablesLeft _ _ _ _≡_ p2 (applyEquality (_+N c) a+b=n)
      p4 : c ≡ n
      p4 = canSubtractFromEqualityLeft p3

  help28 : {a b c n : ℕ} → (n<a+'b+c : n <N a +N (b +N c)) → (a +N b ≡ n) → subtractionNResult.result (-N (inl n<a+'b+c)) ≡ c
  help28 {a} {b} {c} {n} pr a+b=n = canSubtractFromEqualityLeft p2
    where
      p1 : a +N (b +N c) ≡ n +N c
      p1 rewrite Semiring.+Associative ℕSemiring a b c | a+b=n = refl
      p2 : n +N subtractionNResult.result (-N (inl pr)) ≡ n +N c
      p2 = identityOfIndiscernablesLeft _ _ _ _≡_ p1 (equalityCommutative (addMinus' (inl pr)))

  help27 : {a b c n : ℕ} → (a +N b ≡ succ n) → (a +N (b +N c) <N succ n) → a +N (b +N c) ≡ c
  help27 {a} {b} {zero} {n} a+b=sn a+b+c<sn rewrite Semiring.commutative ℕSemiring b 0 | a+b=sn = exFalso (TotalOrder.irreflexive ℕTotalOrder a+b+c<sn)
  help27 {a} {b} {succ c} {n} a+b=sn a+b+c<sn rewrite Semiring.+Associative ℕSemiring a b (succ c) | a+b=sn = exFalso (cannotAddAndEnlarge' a+b+c<sn)

  help26 : {a b c n : ℕ} → (a +N b ≡ n) → (a +N (b +N c) ≡ n) → 0 ≡ c
  help26 {a} {b} {c} {n} a+b=n a+b+c=n rewrite Semiring.+Associative ℕSemiring a b c | a+b=n | Semiring.commutative ℕSemiring n c = equalityCommutative (canSubtractFromEqualityRight a+b+c=n)

  help25 : {a b c n : ℕ} → (a +N b ≡ n) → (b +N c ≡ n) → (a +N 0 ≡ c)
  help25 {a} {b} {c} {n} a+b=n b+c=n rewrite Semiring.commutative ℕSemiring a 0 | Semiring.commutative ℕSemiring a b | equalityCommutative a+b=n = equalityCommutative (canSubtractFromEqualityLeft b+c=n)

  help24 : {a n : ℕ} → (a <N n) → (n <N a +N 0) → False
  help24 {a} {n} a<n n<a+0 rewrite Semiring.commutative ℕSemiring a 0 = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive a<n n<a+0)

  help23 : {a n : ℕ} → (a <N n) → (a +N 0 ≡ n) → False
  help23 {a} {n} a<n a+0=n rewrite Semiring.commutative ℕSemiring a 0 | a+0=n = TotalOrder.irreflexive ℕTotalOrder a<n

  help22 : {a b c n : ℕ} → (a +N b ≡ n) → (c ≡ n) → (n<b+c : n <N b +N c) → (n <N a +N subtractionNResult.result (-N (inl n<b+c))) → False
  help22 {a} {b} {c} {.c} a+b=n refl n<b+c pr = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesRight _ _ _ _<N_ pr4 a+b=n)
    where
      pr1 : c +N c <N a +N (subtractionNResult.result (-N (inl n<b+c)) +N c)
      pr1 = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequality c pr) (equalityCommutative (Semiring.+Associative ℕSemiring a _ c))
      pr2 : c +N c <N a +N (b +N c)
      pr2 = identityOfIndiscernablesRight _ _ _ _<N_ pr1 (applyEquality (a +N_) (addMinus (inl n<b+c)))
      pr3 : c +N c <N (a +N b) +N c
      pr3 = identityOfIndiscernablesRight _ _ _ _<N_ pr2 (Semiring.+Associative ℕSemiring a b c)
      pr4 : c <N a +N b
      pr4 = subtractionPreservesInequality c pr3

  help21 : {a b c n : ℕ} → (a +N b ≡ n) → (b +N c ≡ n) → (c ≡ n) → (a <N n) → False
  help21 {a} {b} {c} {.c} a+b=n b+c=n refl a<n = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _ _ _ _<N_ a<n a=c)
    where
      b=0 : b ≡ 0
      a=c : a ≡ c
      a=c = identityOfIndiscernablesLeft _ _ _ _≡_ a+b=n lemm
        where
          lemm : a +N b ≡ a
          lemm rewrite b=0 | Semiring.commutative ℕSemiring a 0 = refl
      b=0' : (b c : ℕ) → (b +N c ≡ c) → b ≡ 0
      b=0' zero c b+c=c = refl
      b=0' (succ b) zero b+c=c = exFalso (naughtE (equalityCommutative b+c=c))
      b=0' (succ b) (succ c) b+c=c = b=0' (succ b) c bl2
        where
          bl2 : succ b +N c ≡ c
          bl2 rewrite Semiring.commutative ℕSemiring b c | Semiring.commutative ℕSemiring (succ c) b = succInjective b+c=c
      b=0 = b=0' b c b+c=n

  help20 : {a b c n : ℕ} → (c ≡ n) → (a +N b ≡ n) → (n<b+c : n <N b +N c) → (a +N subtractionNResult.result (-N (inl n<b+c)) <N n) → False
  help20 {a} {b} {c} {n} c=n a+b=n n<b+c pr = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _ _ _ _<N_ pr5 c=n)
    where
      pr1 : a +N (subtractionNResult.result (-N (inl n<b+c)) +N n) <N n +N n
      pr1 = identityOfIndiscernablesLeft _ _ _ _<N_ (additionPreservesInequality n pr) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      pr2 : a +N (b +N c) <N n +N n
      pr2 = identityOfIndiscernablesLeft _ _ _ _<N_ pr1 (applyEquality (a +N_) (addMinus (inl n<b+c)))
      pr3 : (a +N b) +N c <N n +N n
      pr3 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = pr2
      pr4 : c +N n <N n +N n
      pr4 = identityOfIndiscernablesLeft _ _ _ _<N_ pr3 (transitivity (applyEquality (_+N c) a+b=n) (Semiring.commutative ℕSemiring n c))
      pr5 : c <N n
      pr5 = subtractionPreservesInequality n pr4

  help19 : {a b c n : ℕ} → (b+c<n : b +N c <N n) → (n<a+b : n <N a +N b) → (a <N n) → (subtractionNResult.result (-N (inl n<a+b)) +N c ≡ n) → False
  help19 {a} {b} {c} {n} b+c<n n<a+b a<n pr = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _ _ _ _<N_ r q')
    where
      p : (n +N subtractionNResult.result (-N (inl n<a+b))) +N c ≡ n +N n
      p = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (n +N_ ) pr) (Semiring.+Associative ℕSemiring n _ c)
      q : (a +N b) +N c ≡ n +N n
      q = identityOfIndiscernablesLeft _ _ _ _≡_ p (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      q' : a +N (b +N c) ≡ n +N n
      q' = identityOfIndiscernablesLeft _ _ _ _≡_ q (equalityCommutative (Semiring.+Associative ℕSemiring a b c))
      r : a +N (b +N c) <N n +N n
      r = addStrongInequalities a<n b+c<n

  help18 : {a b c n : ℕ} → (b+c<n : b +N c <N n) → (n<a+b : n <N a +N b) → (a <N n) → (n <N subtractionNResult.result (-N (inl n<a+b)) +N c) → False
  help18 {a} {b} {c} {n} b+c<n n<a+b a<n pr = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive p4 a<n)
    where
      p : n +N n <N (n +N subtractionNResult.result (-N (inl n<a+b))) +N c
      p = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequalityOnLeft n pr) (Semiring.+Associative ℕSemiring n _ c)
      p' : n +N n <N (a +N b) +N c
      p' = identityOfIndiscernablesRight _ _ _ _<N_ p (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      p2 : n +N n <N a +N (b +N c)
      p2 = identityOfIndiscernablesRight _ _ _ _<N_ p' (equalityCommutative (Semiring.+Associative ℕSemiring a b c))
      p3 : n +N n <N a +N n
      p3 = orderIsTransitive p2 (additionPreservesInequalityOnLeft a b+c<n)
      p4 : n <N a
      p4 = subtractionPreservesInequality n p3

  help17 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → (a +N subtractionNResult.result (-N (inl n<b+c)) <N n) → (subtractionNResult.result (-N (inl n<a+b)) +N c) ≡ n → False
  help17 {a} {b} {c} {n} n<b+c n<a+b p1 p2 = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _ _ _ _<N_ pr1'' pr3)
    where
      pr1' : a +N (subtractionNResult.result (-N (inl n<b+c)) +N n) <N n +N n
      pr1' = identityOfIndiscernablesLeft _ _ _ _<N_ (additionPreservesInequality n p1) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      pr1'' : a +N (b +N c) <N n +N n
      pr1'' = identityOfIndiscernablesLeft _ _ _ _<N_ pr1' (applyEquality (a +N_) (addMinus (inl n<b+c)))
      pr2' : (n +N subtractionNResult.result (-N (inl n<a+b))) +N c ≡ n +N n
      pr2' = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (n +N_) p2) (Semiring.+Associative ℕSemiring n _ c)
      pr2'' : (a +N b) +N c ≡ n +N n
      pr2'' = identityOfIndiscernablesLeft _ _ _ _≡_ pr2' (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      pr3 : a +N (b +N c) ≡ n +N n
      pr3 = identityOfIndiscernablesLeft _ _ _ _≡_ pr2'' (equalityCommutative (Semiring.+Associative ℕSemiring a b c))

  help16 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → (a +N subtractionNResult.result (-N (inl n<b+c))) <N n → (pr : n <N subtractionNResult.result (-N (inl n<a+b)) +N c) → a +N subtractionNResult.result (-N (inl n<b+c)) ≡ subtractionNResult.result (-N (inl pr))
  help16 {a} {b} {c} {n} n<b+c n<a+b pr1 pr2 = exFalso (TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr3 pr1''))
    where
      pr1' : a +N (subtractionNResult.result (-N (inl n<b+c)) +N n) <N n +N n
      pr1' = identityOfIndiscernablesLeft _ _ _ _<N_ (additionPreservesInequality n pr1) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      pr1'' : a +N (b +N c) <N n +N n
      pr1'' = identityOfIndiscernablesLeft _ _ _ _<N_ pr1' (applyEquality (a +N_) (addMinus (inl n<b+c)))
      pr2' : n +N n <N (n +N subtractionNResult.result (-N (inl n<a+b))) +N c
      pr2' = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequalityOnLeft n pr2) (Semiring.+Associative ℕSemiring n _ c)
      pr2'' : n +N n <N (a +N b) +N c
      pr2'' = identityOfIndiscernablesRight _ _ _ _<N_ pr2' (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      pr3 : n +N n <N a +N (b +N c)
      pr3 = identityOfIndiscernablesRight _ _ _ _<N_ pr2'' (equalityCommutative (Semiring.+Associative ℕSemiring a b c))

  help15 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → (n <N a +N subtractionNResult.result (-N (inl n<b+c))) → (subtractionNResult.result (-N (inl n<a+b)) +N c) <N n → False
  help15 {a} {b} {c} {n} n<b+c n<a+b pr1 pr2 = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive p2'' p1')
    where
      p1 : (n +N subtractionNResult.result (-N (inl n<a+b))) +N c <N n +N n
      p1 = identityOfIndiscernablesLeft _ _ _ _<N_ (additionPreservesInequalityOnLeft n pr2) (Semiring.+Associative ℕSemiring n _ c)
      p1' : (a +N b) +N c <N n +N n
      p1' = identityOfIndiscernablesLeft _ _ _ _<N_ p1 (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      p2 : n +N n <N a +N (subtractionNResult.result (-N (inl n<b+c)) +N n)
      p2 = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequality n pr1) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      p2' : n +N n <N a +N (b +N c)
      p2' = identityOfIndiscernablesRight _ _ _ _<N_ p2 (applyEquality (a +N_) (addMinus (inl n<b+c)))
      p2'' : n +N n <N (a +N b) +N c
      p2'' = identityOfIndiscernablesRight _ _ _ _<N_ p2' (Semiring.+Associative ℕSemiring a b c)

  help14 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → (pr1 : n <N a +N subtractionNResult.result (-N (inl n<b+c))) → (pr2 : n <N subtractionNResult.result (-N (inl n<a+b)) +N c) → subtractionNResult.result (-N (inl pr1)) ≡ subtractionNResult.result (-N (inl pr2))
  help14 {a} {b} {c} {n} n<b+c n<a+b pr1 pr2 = equivalentSubtraction _ _ _ _ pr1 pr2 (transitivity (Semiring.+Associative ℕSemiring n _ c) (transitivity (applyEquality (_+N c) (addMinus' (inl n<a+b))) (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring a b c)) (equalityCommutative p2))))
    where
      p1 : (a +N subtractionNResult.result (-N (inl n<b+c))) +N n ≡ a +N (subtractionNResult.result (-N (inl n<b+c)) +N n)
      p1 = equalityCommutative (Semiring.+Associative ℕSemiring a _ n)
      p2 : (a +N subtractionNResult.result (-N (inl n<b+c))) +N n ≡ a +N (b +N c)
      p2 = identityOfIndiscernablesRight _ _ _ _≡_ p1 (applyEquality (a +N_) (addMinus (inl n<b+c)))

  help13 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → (n <N a +N subtractionNResult.result (-N (inl n<b+c))) → (subtractionNResult.result (-N (inl n<a+b)) +N c ≡ n) → False
  help13 {a} {b} {c} {n} n<b+c n<a+b pr1 pr2 = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesRight _ _ _ _<N_ lemm1' lemm3)
    where
      lemm1 : n +N n <N a +N (subtractionNResult.result (-N (inl n<b+c)) +N n)
      lemm1 = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequality n pr1) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      lemm1' : n +N n <N a +N (b +N c)
      lemm1' = identityOfIndiscernablesRight _ _ _ _<N_ lemm1 (applyEquality (a +N_) (addMinus (inl n<b+c)))
      lemm2 : (n +N subtractionNResult.result (-N (inl n<a+b))) +N c ≡ n +N n
      lemm2 = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (n +N_) pr2) (Semiring.+Associative ℕSemiring n _ c)
      lemm2' : (a +N b) +N c ≡ n +N n
      lemm2' = identityOfIndiscernablesLeft _ _ _ _≡_ lemm2 (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      lemm3 : a +N (b +N c) ≡ n +N n
      lemm3 rewrite Semiring.+Associative ℕSemiring a b c = lemm2'

  help12 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → (a +N subtractionNResult.result (-N (inl n<b+c))) ≡ n → subtractionNResult.result (-N (inl n<a+b)) +N c <N n → False
  help12 {a} {b} {c} {n} n<b+c n<a+b pr1 pr2 = TotalOrder.irreflexive ℕTotalOrder lemm4
    where
      pr : {a b c : ℕ} → a +N (b +N c) ≡ b +N (a +N c)
      pr {a} {b} {c} rewrite Semiring.+Associative ℕSemiring a b c | Semiring.commutative ℕSemiring a b | equalityCommutative (Semiring.+Associative ℕSemiring b a c) = refl
      lemm1 : (n +N subtractionNResult.result (-N (inl n<a+b))) +N c <N n +N n
      lemm1 = identityOfIndiscernablesLeft _ _ _ _<N_ (additionPreservesInequalityOnLeft n pr2) (Semiring.+Associative ℕSemiring n _ c)
      lemm2 : (a +N b) +N c <N n +N n
      lemm2 = identityOfIndiscernablesLeft _ _ _ _<N_ lemm1 (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      lemm1' : a +N (subtractionNResult.result (-N (inl n<b+c)) +N n) ≡ n +N n
      lemm1' = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (_+N n) pr1) (equalityCommutative (Semiring.+Associative ℕSemiring a _ n))
      lemm2' : a +N (b +N c) ≡ n +N n
      lemm2' = identityOfIndiscernablesLeft _ _ _ _≡_ lemm1' (applyEquality (a +N_) (addMinus (inl n<b+c)))
      lemm3 : (a +N b) +N c ≡ n +N n
      lemm3 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = lemm2'
      lemm4 : (a +N b) +N c <N (a +N b) +N c
      lemm4 = identityOfIndiscernablesRight _ _ _ _<N_ lemm2 (equalityCommutative lemm3)

  help11 : {a b c n : ℕ} → (a <N n) → (b +N c ≡ n) → (n<a+b : n <N a +N b) → (n <N subtractionNResult.result (-N (inl n<a+b)) +N c) → False
  help11 {a} {b} {c} {n} a<n b+c=n n<a+b pr1 = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive a<n lemm5)
    where
      pr : {a b c : ℕ} → a +N (b +N c) ≡ b +N (a +N c)
      pr {a} {b} {c} rewrite Semiring.+Associative ℕSemiring a b c | Semiring.commutative ℕSemiring a b | equalityCommutative (Semiring.+Associative ℕSemiring b a c) = refl
      lemm : n +N n <N (n +N subtractionNResult.result (-N (inl n<a+b))) +N c
      lemm = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequalityOnLeft n pr1) (Semiring.+Associative ℕSemiring n _ c)
      lemm2 : n +N n <N (a +N b) +N c
      lemm2 = identityOfIndiscernablesRight _ _ _ _<N_ lemm (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      lemm3 : n +N n <N a +N (b +N c)
      lemm3 = identityOfIndiscernablesRight _ _ _ _<N_ lemm2 (equalityCommutative (Semiring.+Associative ℕSemiring a b c))
      lemm4 : n +N n <N a +N n
      lemm4 = identityOfIndiscernablesRight _ _ _ _<N_ lemm3 (applyEquality (a +N_) b+c=n)
      lemm5 : n <N a
      lemm5 = subtractionPreservesInequality n lemm4

  help10 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → (a +N subtractionNResult.result (-N (inl n<b+c)) ≡ n) → (n <N subtractionNResult.result (-N (inl n<a+b)) +N c) → False
  help10 {a} {b} {c} {n} n<b+c n<a+b pr1 pr2 = TotalOrder.irreflexive ℕTotalOrder lemm6
    where
      pr : {a b c : ℕ} → a +N (b +N c) ≡ b +N (a +N c)
      pr {a} {b} {c} rewrite Semiring.+Associative ℕSemiring a b c | Semiring.commutative ℕSemiring a b | equalityCommutative (Semiring.+Associative ℕSemiring b a c) = refl
      lemm : a +N (n +N subtractionNResult.result (-N (inl n<b+c))) ≡ n +N n
      lemm = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (n +N_) pr1) (pr {n} {a})
      lemm2 : a +N (b +N c) ≡ n +N n
      lemm2 = identityOfIndiscernablesLeft _ _ _ _≡_ lemm (applyEquality (a +N_) (addMinus' (inl n<b+c)))
      lemm3 : n +N n <N (n +N subtractionNResult.result (-N (inl n<a+b))) +N c
      lemm3 = identityOfIndiscernablesRight _ _ _ _<N_ (additionPreservesInequalityOnLeft n pr2) (Semiring.+Associative ℕSemiring n _ c)
      lemm4 : n +N n <N (a +N b) +N c
      lemm4 = identityOfIndiscernablesRight _ _ _ _<N_ lemm3 (applyEquality (_+N c) (addMinus' (inl n<a+b)))
      lemm5 : n +N n <N a +N (b +N c)
      lemm5 = identityOfIndiscernablesRight _ _ _ _<N_ lemm4 (equalityCommutative (Semiring.+Associative ℕSemiring a b c))
      lemm6 : a +N (b +N c) <N a +N (b +N c)
      lemm6 = identityOfIndiscernablesLeft _ _ _ _<N_ lemm5 (equalityCommutative lemm2)

  help9 : {a n : ℕ} → (a +N 0 ≡ n) → (a <N n) → False
  help9 {a} {n} n=a+0 a<n rewrite Semiring.commutative ℕSemiring a 0 | n=a+0 = TotalOrder.irreflexive ℕTotalOrder a<n

  help8 : {a n : ℕ} → (n <N a +N 0) → (a <N n) → False
  help8 {a} {n} n<a+0 a<n rewrite Semiring.commutative ℕSemiring a 0 = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive a<n n<a+0)

  help6 : {a b c n : ℕ} → (b +N c ≡ n) → (n<a+b : n <N a +N b) → (a +N 0 ≡ subtractionNResult.result (-N (inl n<a+b)) +N c)
  help6 {a} {b} {c} {n} b+c=n n<a+b rewrite Semiring.commutative ℕSemiring a 0 = canSubtractFromEqualityLeft {n} lem'
    where
      lem : n +N a ≡ (n +N subtractionNResult.result (-N (inl n<a+b))) +N c
      lem rewrite addMinus' (inl n<a+b) | equalityCommutative (Semiring.+Associative ℕSemiring a b c) | b+c=n = Semiring.commutative ℕSemiring n a
      lem' : n +N a ≡ n +N (subtractionNResult.result (-N (inl n<a+b)) +N c)
      lem' = identityOfIndiscernablesRight _ _ _ _≡_ lem (equalityCommutative (Semiring.+Associative ℕSemiring n _ c))

  help5 : {a b c n : ℕ} → (n<b+c : n <N b +N c) → (n<a+b : n <N a +N b) → a +N subtractionNResult.result (-N (inl n<b+c)) ≡ subtractionNResult.result (-N (inl n<a+b)) +N c
  help5 {a} {b} {c} {n} n<b+c n<a+b = canSubtractFromEqualityLeft {n} lemma''
    where
      lemma : a +N (n +N subtractionNResult.result (-N (inl n<b+c))) ≡ (n +N subtractionNResult.result (-N (inl n<a+b))) +N c
      lemma rewrite addMinus' (inl n<b+c) | addMinus' (inl n<a+b) = Semiring.+Associative ℕSemiring a b c
      lemma' : a +N (n +N subtractionNResult.result (-N (inl n<b+c))) ≡ n +N (subtractionNResult.result (-N (inl n<a+b)) +N c)
      lemma' = identityOfIndiscernablesRight _ _ _ _≡_ lemma (equalityCommutative (Semiring.+Associative ℕSemiring n _ c))
      lemma'' : n +N (a +N subtractionNResult.result (-N (inl n<b+c))) ≡ n +N (subtractionNResult.result (-N (inl n<a+b)) +N c)
      lemma'' = identityOfIndiscernablesLeft _ _ _ _≡_ lemma' (pr {a} {n} {subtractionNResult.result (-N (inl n<b+c))})
        where
          pr : {a b c : ℕ} → a +N (b +N c) ≡ b +N (a +N c)
          pr {a} {b} {c} rewrite Semiring.+Associative ℕSemiring a b c | Semiring.commutative ℕSemiring a b | equalityCommutative (Semiring.+Associative ℕSemiring b a c) = refl

  help4 : {a b c n : ℕ} → (n<a+'b+c : n <N a +N (b +N c)) → (n<a+b : n <N a +N b) → (subtractionNResult.result (-N (inl n<a+'b+c)) ≡ subtractionNResult.result (-N (inl n<a+b)) +N c)
  help4 {a} {b} {c} {n} n<a+'b+c n<a+b = canSubtractFromEqualityLeft lemma'
    where
      lemma : (n +N subtractionNResult.result (-N (inl n<a+'b+c))) ≡ (n +N subtractionNResult.result (-N (inl n<a+b))) +N c
      lemma rewrite addMinus' (inl n<a+'b+c) | addMinus' (inl n<a+b) = Semiring.+Associative ℕSemiring a b c
      lemma' : n +N subtractionNResult.result (-N (inl n<a+'b+c)) ≡ n +N (subtractionNResult.result (-N (inl n<a+b)) +N c)
      lemma' = identityOfIndiscernablesRight _ _ _ _≡_ lemma (equalityCommutative (Semiring.+Associative ℕSemiring n (subtractionNResult.result (-N (inl n<a+b))) c))

  help3 : {a b c n : ℕ} → (a <N n) → (b <N n) → (c <N n) → (a +N b <N n) → (pr : n <N b +N c) → a +N subtractionNResult.result (-N (inl pr)) ≡ n → False
  help3 {a} {b} {c} {n} a<n b<n c<n a+b<n n<b+c pr = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive (inter4 inter3) c<n)
    where
      inter : a +N (n +N subtractionNResult.result (-N (inl n<b+c))) ≡ n +N n
      inter = identityOfIndiscernablesLeft _ _ _ _≡_ (applyEquality (n +N_) pr) (lemma n a (subtractionNResult.result (-N (inl n<b+c))))
        where
          lemma : (a b c : ℕ) → a +N (b +N c) ≡ b +N (a +N c)
          lemma a b c rewrite Semiring.+Associative ℕSemiring a b c | Semiring.+Associative ℕSemiring b a c = applyEquality (_+N c) (Semiring.commutative ℕSemiring a b)
      inter2 : n +N n ≡ a +N (b +N c)
      inter2 = equalityCommutative (identityOfIndiscernablesLeft _ _ _ _≡_ inter (applyEquality (a +N_) (addMinus' (inl n<b+c))))
      inter3 : n +N n <N n +N c
      inter3 rewrite inter2 | Semiring.+Associative ℕSemiring a b c = additionPreservesInequality c a+b<n
      inter4 : (n +N n <N n +N c) → n <N c
      inter4 pr rewrite Semiring.commutative ℕSemiring n c = subtractionPreservesInequality n pr

  help2 : {a b c n : ℕ} → (sn<b+c : succ n <N b +N c) → (sn<a+b+c : succ n <N (a +N b) +N c) → a +N subtractionNResult.result (-N (inl sn<b+c)) ≡ subtractionNResult.result (-N (inl sn<a+b+c))
  help2 {a} {b} {c} {n} sn<b+c sn<a+b+c = res inter
    where
      inter : a +N (subtractionNResult.result (-N (inl sn<b+c)) +N succ n) ≡ subtractionNResult.result (-N (inl sn<a+b+c)) +N succ n
      inter rewrite addMinus (inl sn<b+c) | addMinus (inl sn<a+b+c) = Semiring.+Associative ℕSemiring a b c
      res : (a +N (subtractionNResult.result (-N (inl sn<b+c)) +N succ n) ≡ subtractionNResult.result (-N (inl sn<a+b+c)) +N succ n) → a +N subtractionNResult.result (-N (inl sn<b+c)) ≡ subtractionNResult.result (-N (inl sn<a+b+c))
      res pr = canSubtractFromEqualityRight {_} {succ n} (identityOfIndiscernablesLeft _ _ _ _≡_ pr (Semiring.+Associative ℕSemiring a (subtractionNResult.result (-N (inl sn<b+c))) (succ n)))

  help1 : {a b c n : ℕ} → (sn<b+c : succ n <N b +N c) → (pr1 : succ n <N a +N subtractionNResult.result (-N (inl sn<b+c))) → (a +N b <N succ n) → (a <N succ n) → (b <N succ n) → (c <N succ n) → False
  help1 {a} {b} {c} {n} sn<b+c pr1 a+b<sn a<sn b<sn c<sn with -N (inl sn<b+c)
  help1 {a} {b} {c} {n} sn<b+c pr1 a+b<sn a<sn b<sn c<sn | record { result = b+c-sn ; pr = Prb+c-sn } = ans
    where
      b+c-nNonzero : b+c-sn ≡ 0 → False
      b+c-nNonzero pr rewrite (equalityCommutative Prb+c-sn) | pr | Semiring.commutative ℕSemiring n 0 = TotalOrder.irreflexive ℕTotalOrder sn<b+c
      2sn<a+b+c' : succ n +N succ n <N succ n +N (a +N b+c-sn)
      2sn<a+b+c' = additionPreservesInequalityOnLeft (succ n) pr1
      2sn<a+b+c'' : succ n +N succ n <N a +N (succ n +N b+c-sn)
      2sn<a+b+c'' rewrite Semiring.+Associative ℕSemiring a (succ n) b+c-sn | Semiring.commutative ℕSemiring a (succ n) | equalityCommutative (Semiring.+Associative ℕSemiring (succ n) a b+c-sn) = 2sn<a+b+c'
      eep : succ n +N succ n <N a +N (b +N c)
      eep rewrite equalityCommutative Prb+c-sn = 2sn<a+b+c''
      eep2 : a +N (b +N c) <N succ n +N c
      eep2 rewrite Semiring.+Associative ℕSemiring a b c = additionPreservesInequality c a+b<sn
      eep2' : a +N (b +N c) <N succ n +N succ n
      eep2' = orderIsTransitive eep2 (additionPreservesInequalityOnLeft (succ n) c<sn)
      ans : False
      ans = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive eep eep2')

  plusZnAssociative : {n : ℕ} → {pr : 0 <N n} → (a b c : ℤn n pr) → a +n (b +n c) ≡ ((a +n b) +n c)
  plusZnAssociative {zero} {()}
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess} record { x = c ; xLess = cLess } with orderIsTotal (a +N b) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) with orderIsTotal ((a +N b) +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) with orderIsTotal (b +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inl b+c<sn) with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inl b+c<sn) | inl (inl a+'b+c<sn) = equalityZn _ _ (Semiring.+Associative ℕSemiring a b c)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inl b+c<sn) | inl (inr sn<a+'b+c) = exFalso (false {succ n} a+b+c<sn sn<a+'b+c)
    where
      false : {x : ℕ} → (a +N b) +N c <N succ n → succ n <N a +N (b +N c) → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr1 pr2)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inl b+c<sn) | inr sn=a+b+c = exFalso (false a+b+c<sn sn=a+b+c)
    where
      false : {x : ℕ} → (a +N b) +N c <N x → (a +N (b +N c)) ≡ x → False
      false p1 p2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | p2 = TotalOrder.irreflexive ℕTotalOrder p1
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inl _) with orderIsTotal (a +N subtractionNResult.result (-N (inl sn<b+c))) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inl _) | inl (inl x) with -N (inl sn<b+c)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inl a+'b+c<sn) | inl (inl x) | record { result = result ; pr = pr } = exFalso (false a+'b+c<sn pr)
    where
      false : a +N (b +N c) <N succ n → succ n +N result ≡ b +N c → False
      false pr1 pr2 rewrite equalityCommutative pr2 | Semiring.+Associative ℕSemiring a (succ n) result | Semiring.commutative ℕSemiring a (succ n) | equalityCommutative (Semiring.+Associative ℕSemiring (succ n) a result) = cannotAddAndEnlarge' pr1
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inl _) | inl (inr x) with -N (inl sn<b+c)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inl a+'b+c<sn) | inl (inr x) | record { result = result ; pr = pr } = exFalso false
    where
      lemma : a +N (succ n +N result) ≡ a +N (b +N c)
      lemma' : a +N (succ n +N result) <N succ n
      lemma'' : succ n +N (a +N result) <N succ n
      lemma'' = identityOfIndiscernablesLeft _ _ _ _<N_ lemma' (transitivity (Semiring.+Associative ℕSemiring a (succ n) result) (transitivity (applyEquality (λ t → t +N result) (Semiring.commutative ℕSemiring a (succ n))) (equalityCommutative (Semiring.+Associative ℕSemiring (succ n) a result))))
      lemma = applyEquality (λ i → a +N i) pr
      lemma' rewrite lemma = a+'b+c<sn
      false : False
      false = cannotAddAndEnlarge' lemma''
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inl _) | inr x with -N (inl sn<b+c)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inl a+'b+c<sn) | inr x | record { result = result ; pr = pr } = exFalso false
    where
      lemma : a +N (succ n +N result) <N succ n
      lemma rewrite pr = a+'b+c<sn
      lemma' : succ n +N (a +N result) <N succ n
      lemma' = identityOfIndiscernablesLeft _ _ _ _<N_ lemma (transitivity (Semiring.+Associative ℕSemiring a (succ n) result) (transitivity (applyEquality (λ t → t +N result) (Semiring.commutative ℕSemiring a (succ n))) (equalityCommutative (Semiring.+Associative ℕSemiring (succ n) a result))))
      false : False
      false = cannotAddAndEnlarge' lemma'
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inl (inr x) = equalityZn _ _ (exFalso (false {succ n} a+b+c<sn x))
    where
      false : {x : ℕ} → (a +N b) +N c <N succ n → succ n <N a +N (b +N c) → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr1 pr2)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inl (inr sn<b+c) | inr x = exFalso (false a+b+c<sn x)
    where
      false : (a +N b) +N c <N succ n → a +N (b +N c) ≡ succ n → False
      false pr1 pr2 rewrite equalityCommutative pr2 | equalityCommutative (Semiring.+Associative ℕSemiring a b c) = TotalOrder.irreflexive ℕTotalOrder pr1
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inl a+b+c<sn) | inr sn=b+c = exFalso (false a+b+c<sn sn=b+c)
    where
      false : (a +N b) +N c <N succ n → b +N c ≡ succ n → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr2 | Semiring.commutative ℕSemiring a (succ n) = cannotAddAndEnlarge' a+b+c<sn
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) with orderIsTotal (b +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inl b+c<sn) with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inl b+c<sn) | inl (inl a+'b+c<sn) = exFalso (false sn<a+b+c a+'b+c<sn)
    where
      false : (succ n <N (a +N b) +N c) → a +N (b +N c) <N succ n → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr1 pr2)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inl b+c<sn) | inl (inr sn<a+'b+c) = equalityZn _ _ ans
    where
      lemma : succ n +N ((a +N b) +N c) ≡ (a +N (b +N c)) +N succ n
      lemma rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = Semiring.commutative ℕSemiring (succ n) _
      ans : subtractionNResult.result (-N (inl sn<a+'b+c)) ≡ subtractionNResult.result (-N (inl sn<a+b+c))
      ans = equivalentSubtraction _ _ _ _ sn<a+'b+c sn<a+b+c lemma
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inl b+c<sn) | inr x = exFalso (false sn<a+b+c x)
    where
      false : succ n <N (a +N b) +N c → (a +N (b +N c)) ≡ succ n → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr2 = TotalOrder.irreflexive ℕTotalOrder sn<a+b+c
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inr sn<b+c) with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inr sn<b+c) | inl (inl a+b+c<sn) = exFalso (false sn<a+b+c a+b+c<sn)
    where
      false : succ n <N (a +N b) +N c → (a +N (b +N c)) <N succ n → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr1 pr2)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inr sn<b+c) | inl (inr _) with orderIsTotal (a +N subtractionNResult.result (-N (inl sn<b+c))) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inr sn<b+c) | inl (inr _) | inl (inl x) = equalityZn _ _ (help2 {a} {b} {c} {n} sn<b+c sn<a+b+c)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inr sn<b+c) | inl (inr _) | inl (inr x) = equalityZn _ _ (exFalso (help1 sn<b+c x a+b<sn aLess bLess cLess))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inr sn<b+c) | inl (inr _) | inr x = exFalso (help3 aLess bLess cLess a+b<sn sn<b+c x)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inl (inr sn<b+c) | inr a+b+c=sn = exFalso (false sn<a+b+c a+b+c=sn)
    where
      false : (succ n <N (a +N b) +N c) → (a +N (b +N c) ≡ succ n) → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr2 = TotalOrder.irreflexive ℕTotalOrder pr1
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inr sn=b+c with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inr sn=b+c | inl (inl x) = exFalso (false sn<a+b+c x)
    where
      false : succ n <N (a +N b) +N c → a +N (b +N c) <N succ n → False
      false p1 p2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive p1 p2)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inr sn=b+c | inl (inr _) with orderIsTotal (a +N 0) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inr sn=b+c | inl (inr _) | inl (inl x) = equalityZn _ _ (ans sn=b+c)
    where
      ans : b +N c ≡ succ n → a +N 0 ≡ subtractionNResult.result (-N (inl sn<a+b+c))
      ans pr with -N (inl sn<a+b+c)
      ans b+c=sn | record { result = result ; pr = pr1 } rewrite Semiring.commutative ℕSemiring a 0 | equalityCommutative (Semiring.+Associative ℕSemiring a b c) | b+c=sn | Semiring.commutative ℕSemiring (succ n) result = equalityCommutative (canSubtractFromEqualityRight pr1)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inr sn=b+c | inl (inr _) | inl (inr x) = exFalso (false b a+b<sn x)
    where
      false : (b : ℕ) → a +N b <N succ n → succ n <N a +N 0 → False
      false zero pr1 pr2 rewrite Semiring.commutative ℕSemiring a 0 = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr1 pr2)
      false (succ b) pr1 pr2 rewrite Semiring.commutative ℕSemiring a 0 = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr2 (orderIsTransitive (le b (Semiring.commutative ℕSemiring (succ b) a)) pr1))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inr sn=b+c | inl (inr _) | inr x = exFalso (false b a+b<sn x)
    where
      false : (b : ℕ) → a +N b <N succ n → a +N 0 ≡ succ n → False
      false zero pr1 pr2 rewrite pr2 = TotalOrder.irreflexive ℕTotalOrder pr1
      false (succ b) pr1 pr2 rewrite Semiring.commutative ℕSemiring a 0 | pr2 = cannotAddAndEnlarge' pr1
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inl (inr sn<a+b+c) | inr sn=b+c | inr x = exFalso (false sn<a+b+c x)
    where
      false : succ n <N (a +N b) +N c → a +N (b +N c) ≡ succ n → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr2 = TotalOrder.irreflexive ℕTotalOrder pr1
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c with orderIsTotal (b +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inl (inl b+c<sn) with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inl (inl b+c<sn) | inl (inl a+'b+c<sn) = exFalso (false sn=a+b+c a+'b+c<sn)
    where
      false : (a +N b) +N c ≡ succ n → a +N (b +N c) <N succ n → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr1 = TotalOrder.irreflexive ℕTotalOrder pr2
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inl (inl b+c<sn) | inl (inr sn<a+'b+c) = exFalso (false sn=a+b+c sn<a+'b+c)
    where
      false : (a +N b) +N c ≡ succ n → succ n <N a +N (b +N c) → False
      false pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr1 = TotalOrder.irreflexive ℕTotalOrder pr2
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inl (inl b+c<sn) | inr _ = equalityZn _ _ refl
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inl (inr sn<b+c) = exFalso (false a sn=a+b+c sn<b+c)
    where
      false : (a : ℕ) → (a +N b) +N c ≡ succ n → succ n <N b +N c → False
      false zero pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | equalityCommutative pr1 = TotalOrder.irreflexive ℕTotalOrder pr2
      false (succ a) pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | equalityCommutative pr1 = TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive pr2 (le a refl))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inr b+c=sn with orderIsTotal (a +N 0) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inr b+c=sn | inl (inl a+0<sn) = equalityZn _ _ ans
    where
      a=0 : (a : ℕ) → (a +N b) +N c ≡ succ n → b +N c ≡ succ n → a ≡ 0
      a=0 zero pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr2 = refl
      a=0 (succ a) pr1 pr2 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr2 = canSubtractFromEqualityRight pr1
      ans : a +N 0 ≡ 0
      ans rewrite Semiring.commutative ℕSemiring a 0 = a=0 a sn=a+b+c b+c=sn
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inr b+c=sn | inl (inr sn<a+0) = exFalso (false sn<a+0 sn=a+b+c b+c=sn)
    where
      false : succ n <N a +N 0 → (a +N b) +N c ≡ succ n → b +N c ≡ succ n → False
      false pr1 pr2 pr3 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr3 | Semiring.commutative ℕSemiring a 0 = zeroNeverGreater {succ n} (identityOfIndiscernablesRight _ _ _ _<N_ pr1 (a=0 a pr2))
        where
          a=0 : (a : ℕ) → (a +N succ n ≡ succ n) → a ≡ 0
          a=0 zero pr = refl
          a=0 (succ a) pr = canSubtractFromEqualityRight pr
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inl a+b<sn) | inr sn=a+b+c | inr b+c=sn | inr sn=a+0 = exFalso (false sn=a+b+c b+c=sn sn=a+0)
    where
      false : (a +N b) +N c ≡ succ n → b +N c ≡ succ n → a +N 0 ≡ succ n → False
      false pr1 pr2 pr3 rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | pr2 | equalityCommutative pr3 | Semiring.commutative ℕSemiring a 0 = naughtE (identityOfIndiscernablesLeft _ _ _ _≡_ pr3 (a=0 a pr1))
        where
          a=0 : (a : ℕ) → (a +N a ≡ a) → a ≡ 0
          a=0 zero pr = refl
          a=0 (succ a) pr = exFalso (naughtE {a} (equalityCommutative (canSubtractFromEqualityRight pr)))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) with orderIsTotal (b +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inl b+c<sn) with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inl b+c<sn) | inl (inl a+'b+c<sn) = exFalso (false sn<a+b a+'b+c<sn)
    where
      false : succ n <N a +N b → a +N (b +N c) <N succ n → False
      false pr1 pr2 rewrite Semiring.+Associative ℕSemiring a b c = cannotAddAndEnlarge' (orderIsTransitive pr2 pr1)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inl b+c<sn) | inl (inr sn<a+'b+c) with orderIsTotal (subtractionNResult.result (-N (inl sn<a+b)) +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inl b+c<sn) | inl (inr sn<a+'b+c) | inl (inl x) = equalityZn _ _ (help4 {a} {b} {c} {succ n} sn<a+'b+c sn<a+b)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inl b+c<sn) | inl (inr sn<a+'b+c) | inl (inr x) = exFalso (help18 {a} {b} {c} {succ n} b+c<sn sn<a+b aLess x)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inl b+c<sn) | inl (inr sn<a+'b+c) | inr x = exFalso (help19 {a} {b} {c} {succ n} b+c<sn sn<a+b aLess x)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inl b+c<sn) | inr a+'b+c=sn = exFalso (false sn<a+b a+'b+c=sn)
    where
      false : (succ n <N a +N b) → a +N (b +N c) ≡ succ n → False
      false pr1 pr2 rewrite Semiring.+Associative ℕSemiring a b c | equalityCommutative pr2 = cannotAddAndEnlarge' pr1
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) with orderIsTotal (a +N subtractionNResult.result (-N (inl sn<b+c))) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inl x) with orderIsTotal (subtractionNResult.result (-N (inl sn<a+b)) +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inl x) | inl (inl x₁) = equalityZn _ _ (help5 {a} {b} {c} {succ n} sn<b+c sn<a+b)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inl x) | inl (inr x1) = equalityZn _ _ (help16 {a} {b} {c} {succ n} sn<b+c sn<a+b x x1)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inl x) | inr x1 = exFalso (help17 {a} {b} {c} {succ n} sn<b+c sn<a+b x x1)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inr x) with orderIsTotal (subtractionNResult.result (-N (inl sn<a+b)) +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inr x) | inl (inl x1) = equalityZn _ _ (exFalso (help15 {a} {b} {c} {succ n} sn<b+c sn<a+b x x1))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inr x) | inl (inr x1) = equalityZn _ _ (help14 {a} {b} {c} {succ n} sn<b+c sn<a+b x x1)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inl (inr x) | inr x1 = equalityZn _ _ (exFalso (help13 {a} {b} {c} {succ n} sn<b+c sn<a+b x x1))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inr x with orderIsTotal (subtractionNResult.result (-N (inl sn<a+b)) +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inr x | inl (inl x1) = equalityZn _ _ (exFalso (help12 {a} {b} {c} {succ n} sn<b+c sn<a+b x x1))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inr x | inl (inr x1) = equalityZn _ _ (exFalso (help10 {a} {b} {c} {succ n} sn<b+c sn<a+b x x1))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inl (inr sn<b+c) | inr x | inr x₁ = equalityZn _ _ refl
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inr b+c=sn with orderIsTotal (a +N 0) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inr b+c=sn | inl (inl a+0<sn) with orderIsTotal (subtractionNResult.result (-N (inl sn<a+b)) +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inr b+c=sn | inl (inl a+0<sn) | inl (inl x) = equalityZn _ _ (help6 {a} {b} {c} {succ n} b+c=sn sn<a+b)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inr b+c=sn | inl (inl _) | inl (inr x) = equalityZn _ _ (exFalso (help11 {a} {b} {c} {succ n} aLess b+c=sn sn<a+b x))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inr b+c=sn | inl (inl a+0<sn) | inr x = equalityZn _ _ (exFalso (help7 {a} {b} {c} {succ n} b+c=sn aLess sn<a+b x))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inr b+c=sn | inl (inr sn<a+0) = exFalso (help8 {a} {succ n} sn<a+0 aLess)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inl (inr sn<a+b) | inr b+c=sn | inr a+0=sn = exFalso (help9 {a} {succ n} a+0=sn aLess)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b with orderIsTotal c (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) with orderIsTotal (b +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inl b+c<sn) with orderIsTotal (a +N (b +N c)) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inl b+c<sn) | inl (inl a+'b+c<sn) = equalityZn _ _ (help27 {a} {b} {c} {n} sn=a+b a+'b+c<sn)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inl b+c<sn) | inl (inr sn<a+'b+c) = equalityZn _ _ (help28 {a} {b} {c} {succ n} sn<a+'b+c sn=a+b)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inl b+c<sn) | inr a+'b+c=sn = equalityZn _ _ (help26 {a} {b} {c} {succ n} sn=a+b a+'b+c=sn)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inr sn<b+c) with orderIsTotal (a +N subtractionNResult.result (-N (inl sn<b+c))) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inr sn<b+c) | inl (inl x) = equalityZn _ _ (help31 {a} {b} {c} {succ n} sn=a+b sn<b+c)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inr sn<b+c) | inl (inr x) = exFalso (help30 {a} {b} {c} {succ n} cLess sn=a+b sn<b+c x)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inl (inr sn<b+c) | inr x = exFalso (help29 {a} {b} {c} {succ n} cLess sn<b+c x sn=a+b)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inr b+c=sn with orderIsTotal (a +N 0) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inr b+c=sn | inl (inl a+0<sn) = equalityZn _ _ (help25 {a} {b} {c} {succ n} sn=a+b b+c=sn)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inr b+c=sn | inl (inr sn<a+0) = exFalso (help24 {a} {succ n} aLess sn<a+0)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inl c<sn) | inr b+c=sn | inr a+0=sn = exFalso (help23 {a} {succ n} aLess a+0=sn)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inl (inr sn<c) = exFalso (TotalOrder.irreflexive ℕTotalOrder (orderIsTransitive sn<c cLess))
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inr c=sn with orderIsTotal (b +N c) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inr c=sn | inl (inl b+c<sn) = exFalso (help b+c<sn)
    where
      help : (b +N c <N succ n) → False
      help b+c<sn rewrite equalityCommutative c=sn | Semiring.commutative ℕSemiring b c = cannotAddAndEnlarge' b+c<sn
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inr c=sn | inl (inr sn<b+c) with orderIsTotal (a +N subtractionNResult.result (-N (inl sn<b+c))) (succ n)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inr c=sn | inl (inr sn<b+c) | inl (inl x) = exFalso (help20 {a} {b} {c} {succ n} c=sn sn=a+b sn<b+c x)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inr c=sn | inl (inr sn<b+c) | inl (inr x) = exFalso (help22 {a} {b} {c} {succ n} sn=a+b c=sn sn<b+c x)
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inr c=sn | inl (inr sn<b+c) | inr x = equalityZn _ _ refl
  plusZnAssociative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } | inr sn=a+b | inr c=sn | inr b+c=sn = exFalso (help21 {a} {b} {c} {succ n} sn=a+b b+c=sn c=sn aLess)

  subLess : {a b : ℕ} → (0<a : 0 <N a) → (a<b : a <N b) → subtractionNResult.result (-N (inl a<b)) <N b
  subLess {zero} {b} 0<a a<b = exFalso (TotalOrder.irreflexive ℕTotalOrder 0<a)
  subLess {succ a} {b} _ a<b with -N (inl a<b)
  ... | record { result = b-a ; pr = pr } = record { x = a ; proof = pr }

  inverseZn : {n : ℕ} → {pr : 0 <N n} → (a : ℤn n pr) → Sg (ℤn n pr) (λ i → i +n a ≡ record { x = 0 ; xLess = pr } )
  inverseZn {zero} {()}
  inverseZn {succ n} {0<n} record { x = zero ; xLess = zeroLess } = record { x = zero ; xLess = zeroLess } , plusZnIdentityLeft _
  inverseZn {succ n} {0<n} record { x = (succ a) ; xLess = aLess } = ans , pr
    where
      ans = record { x = subtractionNResult.result (-N (inl (canRemoveSuccFrom<N aLess))) ; xLess = subLess (succIsPositive a) aLess }
      pr : ans +n record { x = (succ a) ; xLess = aLess } ≡ record { x = 0 ; xLess = 0<n }
      pr with orderIsTotal (subtractionNResult.result (-N (inl (canRemoveSuccFrom<N aLess))) +N (succ a)) (succ n)
      ... | inl (inl x) = exFalso f
        where
          h : subtractionNResult.result (-N (inl (canRemoveSuccFrom<N aLess))) +N succ a ≡ succ n
          h with -N (inl (canRemoveSuccFrom<N aLess))
          h | record { result = result ; pr = pr } rewrite equalityCommutative pr = Semiring.commutative ℕSemiring result (succ a)
          f : False
          f = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _ _ _ _<N_ x h)
      ... | inl (inr x) = exFalso f
        where
          h : subtractionNResult.result (-N (inl (canRemoveSuccFrom<N aLess))) +N succ a ≡ succ n
          h = addMinus {succ a} {succ n} (inl aLess)
          f : False
          f rewrite h = TotalOrder.irreflexive ℕTotalOrder x
      ... | (inr n-a+sa=sn) = equalityZn _ _ refl

  ℤnGroup : (n : ℕ) → (pr : 0 <N n) → Group (reflSetoid (ℤn n pr)) _+n_
  ℤnGroup n pr = record { identity = record { x = 0 ; xLess = pr } ; inverse = λ a → underlying (inverseZn a) ; multAssoc = λ {a} {b} {c} → plusZnAssociative a b c ; multIdentRight = λ {a} → plusZnIdentityRight a ; multIdentLeft = λ {a} → plusZnIdentityLeft a ; invLeft = λ {a} → helpInvLeft a  ; invRight = λ {a} → helpInvRight a ; wellDefined = reflGroupWellDefined }
    where
      helpInvLeft : (a : ℤn n pr) → underlying (inverseZn a) +n a ≡ record { x = 0 ; xLess = pr }
      helpInvLeft a with inverseZn a
      ... | -a , pr-a = pr-a
      helpInvRight : (a : ℤn n pr) → a +n underlying (inverseZn a) ≡ record { x = 0 ; xLess = pr }
      helpInvRight a rewrite plusZnCommutative a (underlying (inverseZn a)) = helpInvLeft a

  ℤnAbGroup : (n : ℕ) → (pr : 0 <N n) → AbelianGroup (ℤnGroup n pr)
  AbelianGroup.commutative (ℤnAbGroup n pr) {a} {b} = plusZnCommutative a b

  ℤnFinite : (n : ℕ) → (pr : 0 <N n) → FiniteGroup (ℤnGroup n pr) (FinSet n)
  SetoidToSet.project (FiniteGroup.toSet (ℤnFinite n pr)) record { x = x ; xLess = xLess } = ofNat x xLess
  SetoidToSet.wellDefined (FiniteGroup.toSet (ℤnFinite n pr)) x y x=y rewrite x=y = refl
  Surjection.property (SetoidToSet.surj (FiniteGroup.toSet (ℤnFinite n pr))) b = record { x = toNat b ; xLess = toNatSmaller b } , ofNatToNat b
  SetoidToSet.inj (FiniteGroup.toSet (ℤnFinite zero ())) x y x=y
  SetoidToSet.inj (FiniteGroup.toSet (ℤnFinite (succ n) pr)) record { x = x ; xLess = xLess } record { x = y ; xLess = yLess } x=y = equalityZn _ _ b
    where
      b : x ≡ y
      b = ofNatInjective x y xLess yLess x=y
  FiniteSet.size (FiniteGroup.finite (ℤnFinite n pr)) = n
  FiniteSet.mapping (FiniteGroup.finite (ℤnFinite n pr)) = id
  FiniteSet.bij (FiniteGroup.finite (ℤnFinite n pr)) = idIsBijective
