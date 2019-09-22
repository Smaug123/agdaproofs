{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Functions
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Definition
open import Groups.Definition
open import Semirings.Definition
open import Orders

module Numbers.BinaryNaturals.Definition where

  data Bit : Set where
    zero : Bit
    one : Bit

  BinNat : Set
  BinNat = List Bit

  ::Inj : {xs ys : BinNat} {i : Bit} → i :: xs ≡ i :: ys → xs ≡ ys
  ::Inj {i = zero} refl = refl
  ::Inj {i = one} refl = refl

  nonEmptyNotEmpty : {a : _} {A : Set a} {l1 : List A} {i : A} → i :: l1 ≡ [] → False
  nonEmptyNotEmpty {l1 = l1} {i} ()

-- TODO - maybe we should do the floating-point style of assuming there's a leading bit and not storing it.
-- That way, everything is already canonical.

  canonical : BinNat → BinNat
  canonical [] = []
  canonical (zero :: n) with canonical n
  canonical (zero :: n) | [] = []
  canonical (zero :: n) | x :: bl = zero :: x :: bl
  canonical (one :: n) = one :: canonical n

  Canonicalised : Set
  Canonicalised = Sg BinNat (λ i → canonical i ≡ i)

  binNatToN : BinNat → ℕ
  binNatToN [] = 0
  binNatToN (zero :: b) = 2 *N binNatToN b
  binNatToN (one :: b) = 1 +N (2 *N binNatToN b)

  incr : BinNat → BinNat
  incr [] = one :: []
  incr (zero :: n) = one :: n
  incr (one :: n) = zero :: (incr n)

  incrNonzero : (x : BinNat) → canonical (incr x) ≡ [] → False

  incrPreservesCanonical : (x : BinNat) → (canonical x ≡ x) → canonical (incr x) ≡ incr x
  incrPreservesCanonical [] pr = refl
  incrPreservesCanonical (zero :: xs) pr with canonical xs
  incrPreservesCanonical (zero :: xs) pr | x :: t = applyEquality (one ::_) (::Inj pr)
  incrPreservesCanonical (one :: xs) pr with inspect (canonical (incr xs))
  incrPreservesCanonical (one :: xs) pr | [] with≡ x = exFalso (incrNonzero xs x)
  incrPreservesCanonical (one :: xs) pr | (x₁ :: y) with≡ x rewrite x = applyEquality (zero ::_) (transitivity (equalityCommutative x) (incrPreservesCanonical xs (::Inj pr)))

  incrPreservesCanonical' : (x : BinNat) → canonical (incr x) ≡ incr (canonical x)

  incrC : Canonicalised → Canonicalised
  incrC (a , b) = incr a , incrPreservesCanonical a b

  NToBinNat : ℕ → BinNat
  NToBinNat zero = []
  NToBinNat (succ n) with NToBinNat n
  NToBinNat (succ n) | t = incr t

  NToBinNatC : ℕ → Canonicalised
  NToBinNatC zero = [] , refl
  NToBinNatC (succ n) = incrC (NToBinNatC n)

  incrInj : {x y : BinNat} → incr x ≡ incr y → canonical x ≡ canonical y

  incrNonzero' : (x : BinNat) → (incr x) ≡ [] → False
  incrNonzero' (zero :: xs) ()
  incrNonzero' (one :: xs) ()

  canonicalRespectsIncr' : {x y : BinNat} → canonical (incr x) ≡ canonical (incr y) → canonical x ≡ canonical y

  binNatToNSucc : (n : BinNat) → binNatToN (incr n) ≡ succ (binNatToN n)
  NToBinNatSucc : (n : ℕ) → incr (NToBinNat n) ≡ NToBinNat (succ n)

  binNatToNZero : (x : BinNat) → binNatToN x ≡ 0 → canonical x ≡ []
  binNatToNZero' : (x : BinNat) → canonical x ≡ [] → binNatToN x ≡ 0

  NToBinNatZero : (n : ℕ) → NToBinNat n ≡ [] → n ≡ 0
  NToBinNatZero zero pr = refl
  NToBinNatZero (succ n) pr with NToBinNat n
  NToBinNatZero (succ n) pr | zero :: bl = exFalso (nonEmptyNotEmpty pr)
  NToBinNatZero (succ n) pr | one :: bl = exFalso (nonEmptyNotEmpty pr)

  canonicalAscends : {i : Bit} → (a : BinNat) → 0 <N binNatToN a → i :: canonical a ≡ canonical (i :: a)

  canonicalAscends' : {i : Bit} → (a : BinNat) → (canonical a ≡ [] → False) → i :: canonical a ≡ canonical (i :: a)
  canonicalAscends' {i} a pr = canonicalAscends {i} a (t a pr)
    where
      t : (a : BinNat) → (canonical a ≡ [] → False) → 0 <N binNatToN a
      t a pr with orderIsTotal 0 (binNatToN a)
      t a pr | inl (inl x) = x
      t a pr | inr x = exFalso (pr (binNatToNZero a (equalityCommutative x)))

  canonicalIdempotent : (a : BinNat) → canonical a ≡ canonical (canonical a)
  canonicalIdempotent [] = refl
  canonicalIdempotent (zero :: a) with inspect (canonical a)
  canonicalIdempotent (zero :: a) | [] with≡ y rewrite y = refl
  canonicalIdempotent (zero :: a) | (x :: bl) with≡ y = transitivity (equalityCommutative (canonicalAscends' {zero} a λ p → contr p y)) (transitivity (applyEquality (zero ::_) (canonicalIdempotent a)) (equalityCommutative v))
    where
      contr : {a : _} {A : Set a} {l1 l2 : List A} → {x : A} → l1 ≡ [] → l1 ≡ x :: l2 → False
      contr {l1 = []} p1 ()
      contr {l1 = x :: l1} () p2
      u : canonical (canonical (zero :: a)) ≡ canonical (zero :: canonical a)
      u = applyEquality canonical (equalityCommutative (canonicalAscends' {zero} a λ p → contr p y))
      v : canonical (canonical (zero :: a)) ≡ zero :: canonical (canonical a)
      v = transitivity u (equalityCommutative (canonicalAscends' {zero} (canonical a) λ p → contr (transitivity (canonicalIdempotent a) p) y))
  canonicalIdempotent (one :: a) rewrite equalityCommutative (canonicalIdempotent a) = refl

  canonicalAscends'' : {i : Bit} → (a : BinNat) → canonical (i :: canonical a) ≡ canonical (i :: a)

  binNatToNInj : (x y : BinNat) → binNatToN x ≡ binNatToN y → canonical x ≡ canonical y

  NToBinNatInj : (x y : ℕ) → canonical (NToBinNat x) ≡ canonical (NToBinNat y) → x ≡ y

  NToBinNatIsCanonical : (x : ℕ) → NToBinNat x ≡ canonical (NToBinNat x)
  NToBinNatIsCanonical zero = refl
  NToBinNatIsCanonical (succ x) with NToBinNatC x
  NToBinNatIsCanonical (succ x) | a , b = equalityCommutative (incrPreservesCanonical (NToBinNat x) (equalityCommutative (NToBinNatIsCanonical x)))

  contr' : {a : _} {A : Set a} {l1 l2 : List A} → {x : A} → l1 ≡ [] → l1 ≡ x :: l2 → False
  contr' {l1 = []} p1 ()
  contr' {l1 = x :: l1} () p2

  binNatToNIsCanonical : (x : BinNat) → binNatToN (canonical x) ≡ binNatToN x
  binNatToNIsCanonical [] = refl
  binNatToNIsCanonical (zero :: x) with inspect (canonical x)
  binNatToNIsCanonical (zero :: x) | [] with≡ t rewrite t | binNatToNZero' x t = refl
  binNatToNIsCanonical (zero :: x) | (x₁ :: bl) with≡ t rewrite (equalityCommutative (canonicalAscends' {zero} x λ p → contr' p t)) | binNatToNIsCanonical x = refl
  binNatToNIsCanonical (one :: x) rewrite binNatToNIsCanonical x = refl

-- The following two theorems demonstrate that Canonicalised is isomorphic to ℕ

  nToN : (x : ℕ) → binNatToN (NToBinNat x) ≡ x

  binToBin : (x : BinNat) → NToBinNat (binNatToN x) ≡ canonical x
  binToBin x = transitivity (NToBinNatIsCanonical (binNatToN x)) (binNatToNInj (NToBinNat (binNatToN x)) x (nToN (binNatToN x)))

  doubleIsBitShift' : (a : ℕ) → NToBinNat (2 *N succ a) ≡ zero :: NToBinNat (succ a)
  doubleIsBitShift' zero = refl
  doubleIsBitShift' (succ a) with doubleIsBitShift' a
  ... | bl rewrite Semiring.commutative ℕSemiring a (succ (succ (a +N 0))) | Semiring.commutative ℕSemiring (succ (a +N 0)) a | Semiring.commutative ℕSemiring a (succ (a +N 0)) | Semiring.commutative ℕSemiring (a +N 0) a | bl = refl

  doubleIsBitShift : (a : ℕ) → (0 <N a) → NToBinNat (2 *N a) ≡ zero :: NToBinNat a
  doubleIsBitShift zero ()
  doubleIsBitShift (succ a) _ = doubleIsBitShift' a

  canonicalDescends : {a : Bit} (as : BinNat) → (prA : a :: as ≡ canonical (a :: as)) → as ≡ canonical as
  canonicalDescends {zero} as pr with canonical as
  canonicalDescends {zero} as pr | x :: bl = ::Inj pr
  canonicalDescends {one} as pr = ::Inj pr

--- Proofs

  parity : (a b : ℕ) → succ (2 *N a) ≡ 2 *N b → False
  doubleInj : (a b : ℕ) → (2 *N a) ≡ (2 *N b) → a ≡ b

  incrNonzeroTwice : (x : BinNat) → canonical (incr (incr x)) ≡ one :: [] → False
  incrNonzeroTwice (zero :: xs) pr with canonical (incr xs)
  incrNonzeroTwice (zero :: xs) () | []
  incrNonzeroTwice (zero :: xs) () | x :: bl
  incrNonzeroTwice (one :: xs) pr = exFalso (incrNonzero xs (::Inj pr))

  canonicalRespectsIncr' {[]} {[]} pr = refl
  canonicalRespectsIncr' {[]} {zero :: y} pr with canonical y
  canonicalRespectsIncr' {[]} {zero :: y} pr | [] = refl
  canonicalRespectsIncr' {[]} {one :: y} pr with canonical (incr y)
  canonicalRespectsIncr' {[]} {one :: y} () | []
  canonicalRespectsIncr' {[]} {one :: y} () | x :: bl
  canonicalRespectsIncr' {zero :: xs} {y} pr with canonical xs
  canonicalRespectsIncr' {zero :: xs} {[]} pr | [] = refl
  canonicalRespectsIncr' {zero :: xs} {zero :: y} pr | [] with canonical y
  canonicalRespectsIncr' {zero :: xs} {zero :: y} pr | [] | [] = refl
  canonicalRespectsIncr' {zero :: xs} {one :: y} pr | [] with canonical (incr y)
  canonicalRespectsIncr' {zero :: xs} {one :: y} () | [] | []
  canonicalRespectsIncr' {zero :: xs} {one :: y} () | [] | x :: bl
  canonicalRespectsIncr' {zero :: xs} {zero :: ys} pr | x :: bl with canonical ys
  canonicalRespectsIncr' {zero :: xs} {zero :: ys} pr | x :: bl | x₁ :: th = applyEquality (zero ::_) (::Inj pr)
  canonicalRespectsIncr' {zero :: xs} {one :: ys} pr | x :: bl with canonical (incr ys)
  canonicalRespectsIncr' {zero :: xs} {one :: ys} () | x :: bl | []
  canonicalRespectsIncr' {zero :: xs} {one :: ys} () | x :: bl | x₁ :: th
  canonicalRespectsIncr' {one :: xs} {[]} pr with canonical (incr xs)
  canonicalRespectsIncr' {one :: xs} {[]} () | []
  canonicalRespectsIncr' {one :: xs} {[]} () | x :: bl
  canonicalRespectsIncr' {one :: xs} {zero :: ys} pr with canonical ys
  canonicalRespectsIncr' {one :: xs} {zero :: ys} pr | [] with canonical (incr xs)
  canonicalRespectsIncr' {one :: xs} {zero :: ys} () | [] | []
  canonicalRespectsIncr' {one :: xs} {zero :: ys} () | [] | x :: t
  canonicalRespectsIncr' {one :: xs} {zero :: ys} pr | x :: bl with canonical (incr xs)
  canonicalRespectsIncr' {one :: xs} {zero :: ys} () | x :: bl | []
  canonicalRespectsIncr' {one :: xs} {zero :: ys} () | x :: bl | x₁ :: t
  canonicalRespectsIncr' {one :: xs} {one :: ys} pr with inspect (canonical (incr xs))
  canonicalRespectsIncr' {one :: xs} {one :: ys} pr | [] with≡ x = exFalso (incrNonzero xs x)
  canonicalRespectsIncr' {one :: xs} {one :: ys} pr | (x+1 :: x+1s) with≡ bad rewrite bad = applyEquality (one ::_) ans
    where
      ans : canonical xs ≡ canonical ys
      ans with inspect (canonical (incr ys))
      ans | [] with≡ x = exFalso (incrNonzero ys x)
      ans | (x₁ :: y) with≡ x rewrite x = canonicalRespectsIncr' {xs} {ys} (transitivity bad (transitivity (::Inj pr) (equalityCommutative x)))

  binNatToNInj[] : (y : BinNat) → 0 ≡ binNatToN y → [] ≡ canonical y
  binNatToNInj[] [] pr = refl
  binNatToNInj[] (zero :: y) pr with productZeroImpliesOperandZero {2} {binNatToN y} (equalityCommutative pr)
  binNatToNInj[] (zero :: y) pr | inr x with inspect (canonical y)
  binNatToNInj[] (zero :: y) pr | inr x | [] with≡ canYPr rewrite canYPr = refl
  binNatToNInj[] (zero :: ys) pr | inr x | (y :: canY) with≡ canYPr with binNatToNZero ys x
  ... | r with canonical ys
  binNatToNInj[] (zero :: ys) pr | inr x | (y :: canY) with≡ canYPr | r | [] = refl
  binNatToNInj[] (zero :: ys) pr | inr x | (y :: canY) with≡ canYPr | () | x₁ :: t

  binNatToNInj [] y pr = binNatToNInj[] y pr
  binNatToNInj (zero :: xs) [] pr = equalityCommutative (binNatToNInj[] (zero :: xs) (equalityCommutative pr))
  binNatToNInj (zero :: xs) (zero :: ys) pr with doubleInj (binNatToN xs) (binNatToN ys) pr
  ... | x=y with binNatToNInj xs ys x=y
  ... | t with canonical xs
  binNatToNInj (zero :: xs) (zero :: ys) pr | x=y | t | [] with canonical ys
  binNatToNInj (zero :: xs) (zero :: ys) pr | x=y | t | [] | [] = refl
  binNatToNInj (zero :: xs) (zero :: ys) pr | x=y | t | x :: cxs with canonical ys
  binNatToNInj (zero :: xs) (zero :: ys) pr | x=y | t | x :: cxs | x₁ :: cys = applyEquality (zero ::_) t
  binNatToNInj (zero :: xs) (one :: ys) pr = exFalso (parity (binNatToN ys) (binNatToN xs) (equalityCommutative pr))
  binNatToNInj (one :: xs) (zero :: ys) pr = exFalso (parity (binNatToN xs) (binNatToN ys) pr)
  binNatToNInj (one :: xs) (one :: ys) pr = applyEquality (one ::_) (binNatToNInj xs ys (doubleInj (binNatToN xs) (binNatToN ys) (succInjective pr)))

  NToBinNatInj zero zero pr = refl
  NToBinNatInj zero (succ y) pr with NToBinNat y
  NToBinNatInj zero (succ y) pr | bl = exFalso (incrNonzero bl (equalityCommutative pr))
  NToBinNatInj (succ x) zero pr with NToBinNat x
  ... | bl = exFalso (incrNonzero bl pr)
  NToBinNatInj (succ x) (succ y) pr with inspect (NToBinNat x)
  NToBinNatInj (succ zero) (succ zero) pr | [] with≡ nToBinXPr = refl
  NToBinNatInj (succ zero) (succ (succ y)) pr | [] with≡ nToBinXPr with NToBinNat y
  NToBinNatInj (succ zero) (succ (succ y)) pr | [] with≡ nToBinXPr | y' = exFalso (incrNonzeroTwice y' (equalityCommutative pr))
  NToBinNatInj (succ (succ x)) (succ y) pr | [] with≡ nToBinXPr with NToBinNat x
  NToBinNatInj (succ (succ x)) (succ y) pr | [] with≡ nToBinXPr | t = exFalso (incrNonzero' t nToBinXPr)
  NToBinNatInj (succ x) (succ y) pr | (x₁ :: nToBinX) with≡ nToBinXPr with NToBinNatInj x y (canonicalRespectsIncr' {NToBinNat x} {NToBinNat y} pr)
  NToBinNatInj (succ x) (succ .x) pr | (x₁ :: nToBinX) with≡ nToBinXPr | refl = refl

  incrInj {[]} {[]} pr = refl
  incrInj {[]} {zero :: ys} pr rewrite equalityCommutative (::Inj pr) = refl
  incrInj {zero :: xs} {[]} pr rewrite ::Inj pr = refl
  incrInj {zero :: xs} {zero :: .xs} refl = refl
  incrInj {one :: xs} {one :: ys} pr = applyEquality (one ::_) (incrInj {xs} {ys} (l (incr xs) (incr ys) pr))
    where
      l : (a : BinNat) → (b : BinNat) → zero :: a ≡ zero :: b → a ≡ b
      l a .a refl = refl

  doubleInj zero zero pr = refl
  doubleInj (succ a) (succ b) pr = applyEquality succ (doubleInj a b u)
    where
      t : a +N a ≡ b +N b
      t rewrite Semiring.commutative ℕSemiring (succ a) 0 | Semiring.commutative ℕSemiring (succ b) 0 | Semiring.commutative ℕSemiring a (succ a) | Semiring.commutative ℕSemiring b (succ b) = succInjective (succInjective pr)
      u : a +N (a +N zero) ≡ b +N (b +N zero)
      u rewrite Semiring.commutative ℕSemiring a 0 | Semiring.commutative ℕSemiring b 0 = t

  binNatToNZero [] pr = refl
  binNatToNZero (zero :: xs) pr with inspect (canonical xs)
  binNatToNZero (zero :: xs) pr | [] with≡ x rewrite x = refl
  binNatToNZero (zero :: xs) pr | (x₁ :: y) with≡ x with productZeroImpliesOperandZero {2} {binNatToN xs} pr
  binNatToNZero (zero :: xs) pr | (x₁ :: y) with≡ x | inr pr' with binNatToNZero xs pr'
  ... | bl with canonical xs
  binNatToNZero (zero :: xs) pr | (x₁ :: y) with≡ x | inr pr' | bl | [] = refl
  binNatToNZero (zero :: xs) pr | (x₁ :: y) with≡ x | inr pr' | () | x₂ :: t

  binNatToNSucc [] = refl
  binNatToNSucc (zero :: n) = refl
  binNatToNSucc (one :: n) rewrite Semiring.commutative ℕSemiring (binNatToN n) zero | Semiring.commutative ℕSemiring (binNatToN (incr n)) 0 | binNatToNSucc n = applyEquality succ (Semiring.commutative ℕSemiring (binNatToN n) (succ (binNatToN n)))

  incrNonzero (one :: xs) pr with inspect (canonical (incr xs))
  incrNonzero (one :: xs) pr | [] with≡ x = incrNonzero xs x
  incrNonzero (one :: xs) pr | (y :: ys) with≡ x with canonical (incr xs)
  incrNonzero (one :: xs) pr | (y :: ys) with≡ () | []
  incrNonzero (one :: xs) () | (.x₁ :: .th) with≡ refl | x₁ :: th

  nToN zero = refl
  nToN (succ x) with inspect (NToBinNat x)
  nToN (succ x) | [] with≡ pr = ans
    where
      t : x ≡ zero
      t = NToBinNatInj x 0 (applyEquality canonical pr)
      ans : binNatToN (incr (NToBinNat x)) ≡ succ x
      ans rewrite t | pr = refl
  nToN (succ x) | (bit :: xs) with≡ pr = transitivity (binNatToNSucc (NToBinNat x)) (applyEquality succ (nToN x))

  parity zero (succ b) pr rewrite Semiring.commutative ℕSemiring b (succ (b +N 0)) = bad pr
    where
      bad : (1 ≡ succ (succ ((b +N 0) +N b))) → False
      bad ()
  parity (succ a) (succ b) pr rewrite Semiring.commutative ℕSemiring b (succ (b +N 0)) | Semiring.commutative ℕSemiring a (succ (a +N 0)) | Semiring.commutative ℕSemiring (a +N 0) a | Semiring.commutative ℕSemiring (b +N 0) b = parity a b (succInjective (succInjective pr))

  binNatToNZero' [] pr = refl
  binNatToNZero' (zero :: xs) pr with inspect (canonical xs)
  binNatToNZero' (zero :: xs) pr | [] with≡ p2 = ans
    where
      t : binNatToN xs ≡ 0
      t = binNatToNZero' xs p2
      ans : 2 *N binNatToN xs ≡ 0
      ans rewrite t = refl
  binNatToNZero' (zero :: xs) pr | (y :: ys) with≡ p rewrite p = exFalso (bad pr)
    where
      bad : zero :: y :: ys ≡ [] → False
      bad ()
  binNatToNZero' (one :: xs) ()

  canonicalAscends {zero} a 0<a with inspect (canonical a)
  canonicalAscends {zero} (zero :: a) 0<a | [] with≡ x = exFalso (contr'' (binNatToN a) t v)
    where
      u : binNatToN (zero :: a) ≡ 0
      u = binNatToNZero' (zero :: a) x
      v : binNatToN a ≡ 0
      v with inspect (binNatToN a)
      v | zero with≡ x = x
      v | succ a' with≡ x with inspect (binNatToN (zero :: a))
      v | succ a' with≡ x | zero with≡ pr2 rewrite pr2 = exFalso (TotalOrder.irreflexive ℕTotalOrder 0<a)
      v | succ a' with≡ x | succ y with≡ pr2 rewrite u = exFalso (TotalOrder.irreflexive ℕTotalOrder 0<a)
      t : 0 <N binNatToN a
      t with binNatToN a
      t | succ bl rewrite Semiring.commutative ℕSemiring (succ bl) 0 = succIsPositive bl
      contr'' : (x : ℕ) → (0 <N x) → (x ≡ 0) → False
      contr'' x 0<x x=0 rewrite x=0 = TotalOrder.irreflexive ℕTotalOrder 0<x
  canonicalAscends {zero} a 0<a | (x₁ :: y) with≡ x rewrite x = refl
  canonicalAscends {one} a 0<a = refl

  canonicalAscends'' {i} a with inspect (canonical a)
  canonicalAscends'' {zero} a | [] with≡ x rewrite x = refl
  canonicalAscends'' {one} a | [] with≡ x rewrite x = refl
  canonicalAscends'' {i} a | (x₁ :: y) with≡ x = transitivity (applyEquality canonical (canonicalAscends' {i} a λ p → contr p x)) (equalityCommutative (canonicalIdempotent (i :: a)))
    where
      contr : {a : _} {A : Set a} {l1 l2 : List A} → {x : A} → l1 ≡ [] → l1 ≡ x :: l2 → False
      contr {l1 = []} p1 ()
      contr {l1 = x :: l1} () p2

  incrPreservesCanonical' [] = refl
  incrPreservesCanonical' (zero :: xs) with inspect (canonical xs)
  incrPreservesCanonical' (zero :: xs) | [] with≡ x rewrite x = refl
  incrPreservesCanonical' (zero :: xs) | (x₁ :: y) with≡ x rewrite x = refl
  incrPreservesCanonical' (one :: xs) with inspect (canonical (incr xs))
  ... | [] with≡ pr = exFalso (incrNonzero xs pr)
  ... | (_ :: _) with≡ pr rewrite pr = applyEquality (zero ::_) (transitivity (equalityCommutative pr) (incrPreservesCanonical' xs))

  NToBinNatSucc zero = refl
  NToBinNatSucc (succ n) with NToBinNat n
  ... | [] = refl
  ... | a :: as = refl
