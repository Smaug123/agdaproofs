{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Functions
open import Lists.Lists
open import Numbers.Naturals
open import Groups.GroupDefinition

module Numbers.BinaryNaturals where

  data Bit : Set where
    zero : Bit
    one : Bit

  BinNat : Set
  BinNat = List Bit

  ::Inj : {xs ys : BinNat} {i : Bit} → i :: xs ≡ i :: ys → xs ≡ ys
  ::Inj refl = refl

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

  binNatToNZero : (x : BinNat) → binNatToN x ≡ 0 → canonical x ≡ []

  binNatToNInj : (x y : BinNat) → binNatToN x ≡ binNatToN y → canonical x ≡ canonical y

  NToBinNatInj : (x y : ℕ) → canonical (NToBinNat x) ≡ canonical (NToBinNat y) → x ≡ y

  NToBinNatIsCanonical : (x : ℕ) → NToBinNat x ≡ canonical (NToBinNat x)
  NToBinNatIsCanonical zero = refl
  NToBinNatIsCanonical (succ x) with NToBinNatC x
  NToBinNatIsCanonical (succ x) | a , b = equalityCommutative (incrPreservesCanonical (NToBinNat x) (equalityCommutative (NToBinNatIsCanonical x)))

-- The following two theorems demonstrate that Canonicalised is isomorphic to ℕ

  nToN : (x : ℕ) → binNatToN (NToBinNat x) ≡ x

  binToBin : (x : BinNat) → NToBinNat (binNatToN x) ≡ canonical x
  binToBin x = transitivity (NToBinNatIsCanonical (binNatToN x)) (binNatToNInj (NToBinNat (binNatToN x)) x (nToN (binNatToN x)))

  _+Binherit_ : BinNat → BinNat → BinNat
  a +Binherit b = NToBinNat (binNatToN a +N binNatToN b)

  _+BinheritC_ : Canonicalised → Canonicalised → Canonicalised
  (a , prA) +BinheritC (b , prB) = NToBinNatC (binNatToN a +N binNatToN b)

  _+B_ : BinNat → BinNat → BinNat
  [] +B b = b
  (x :: a) +B [] = x :: a
  (zero :: xs) +B (y :: ys) = y :: (xs +B ys)
  (one :: xs) +B (zero :: ys) = one :: (xs +B ys)
  (one :: xs) +B (one :: ys) = zero :: incr (xs +B ys)

-- Still not sure of the right way to go about this one. Should we go via canonical, even though it's a big waste in almost all cases?
  doubleIsBitShift : (a : ℕ) → (0 <N a) → NToBinNat (2 *N a) ≡ zero :: NToBinNat a
  doubleIsBitShift zero ()
  doubleIsBitShift (succ a) _ with inspect (NToBinNat (a +N succ (a +N 0)))
  doubleIsBitShift (succ a) _ | t = {!!}

  +BCommutative : (a b : BinNat) → a +B b ≡ b +B a
  +BCommutative [] [] = refl
  +BCommutative [] (x :: b) = refl
  +BCommutative (x :: a) [] = refl
  +BCommutative (zero :: as) (zero :: bs) rewrite +BCommutative as bs = refl
  +BCommutative (zero :: as) (one :: bs) rewrite +BCommutative as bs = refl
  +BCommutative (one :: as) (zero :: bs) rewrite +BCommutative as bs = refl
  +BCommutative (one :: as) (one :: bs) rewrite +BCommutative as bs = refl

  +BIsInherited[] : (b : BinNat) (prB : b ≡ canonical b) → [] +Binherit b ≡ [] +B b
  +BIsInherited[] [] prB = refl
  +BIsInherited[] (zero :: b) prB = t
    where
      refine : (b : BinNat) → zero :: b ≡ canonical (zero :: b) → b ≡ canonical b
      refine b pr with canonical b
      refine b pr | x :: bl = ::Inj pr
      t : NToBinNat (0 +N binNatToN (zero :: b)) ≡ zero :: b
      t with orderIsTotal 0 (binNatToN b)
      t | inl (inl pos) = transitivity (doubleIsBitShift (binNatToN b) pos) (applyEquality (zero ::_) (transitivity (binToBin b) (equalityCommutative (refine b prB))))
      t | inl (inr ())
      ... | inr eq with binNatToNZero b (equalityCommutative eq)
      ... | u with canonical b
      t | inr eq | u | [] = exFalso (bad b prB)
        where
          bad : (c : BinNat) → zero :: c ≡ [] → False
          bad c ()
      t | inr eq | () | x :: bl
  +BIsInherited[] (one :: b) prB = ans
    where
      ans : NToBinNat (binNatToN (one :: b)) ≡ one :: b
      ans = transitivity (binToBin (one :: b)) (equalityCommutative prB)

  canonicalDescends : {a : Bit} (as : BinNat) → (prA : a :: as ≡ canonical (a :: as)) → as ≡ canonical as
  canonicalDescends {zero} as pr with canonical as
  canonicalDescends {zero} as pr | x :: bl = ::Inj pr
  canonicalDescends {one} as pr = ::Inj pr

  +BIsInherited : (a b : BinNat) (prA : a ≡ canonical a) (prB : b ≡ canonical b) → a +Binherit b ≡ a +B b
  +BinheritLemma : (a : BinNat) (b : BinNat) (prA : a ≡ canonical a) (prB : b ≡ canonical b) → incr (NToBinNat ((binNatToN a +N binNatToN b) +N ((binNatToN a +N binNatToN b) +N zero))) ≡ one :: (a +B b)

  +BinheritLemma a b prA prB with orderIsTotal 0 (binNatToN a +N binNatToN b)
  +BinheritLemma a b prA prB | inl (inl x) rewrite doubleIsBitShift (binNatToN a +N binNatToN b) x = applyEquality (one ::_) (+BIsInherited a b prA prB)
  +BinheritLemma a b prA prB | inr x with sumZeroImpliesOperandsZero (binNatToN a) (equalityCommutative x)
  +BinheritLemma a b prA prB | inr x | fst ,, snd = ans2
    where
      bad : b ≡ []
      bad = transitivity prB (binNatToNZero b snd)
      bad2 : a ≡ []
      bad2 = transitivity prA (binNatToNZero a fst)
      ans2 : incr (NToBinNat ((binNatToN a +N binNatToN b) +N ((binNatToN a +N binNatToN b) +N zero))) ≡ one :: (a +B b)
      ans2 rewrite bad | bad2 = refl

  +BIsInherited [] b _ prB = +BIsInherited[] b prB
  +BIsInherited (x :: a) [] prA _ rewrite +BCommutative (x :: a) [] | additionNIsCommutative (binNatToN (x :: a)) (binNatToN []) = +BIsInherited[] (x :: a) prA
  +BIsInherited (zero :: as) (zero :: b) prA prB with orderIsTotal 0 (binNatToN as +N binNatToN b)
  ... | inl (inl 0<) rewrite additionNIsCommutative (binNatToN as) 0 | additionNIsCommutative (binNatToN b) 0 | equalityCommutative (additionNIsAssociative (binNatToN as +N binNatToN as) (binNatToN b) (binNatToN b)) | additionNIsAssociative (binNatToN as) (binNatToN as) (binNatToN b) | additionNIsCommutative (binNatToN as) (binNatToN b) | equalityCommutative (additionNIsAssociative (binNatToN as) (binNatToN b) (binNatToN as)) | additionNIsAssociative (binNatToN as +N binNatToN b) (binNatToN as) (binNatToN b) | additionNIsCommutative 0 ((binNatToN as +N binNatToN b) +N (binNatToN as +N binNatToN b)) | additionNIsAssociative (binNatToN as +N binNatToN b) (binNatToN as +N binNatToN b) 0 = transitivity (doubleIsBitShift (binNatToN as +N binNatToN b) (identityOfIndiscernablesRight _ _ _ _<N_ 0< (additionNIsCommutative (binNatToN b) _))) (applyEquality (zero ::_) (+BIsInherited as b (canonicalDescends as prA) (canonicalDescends b prB)))
  +BIsInherited (zero :: as) (zero :: b) prA prB | inl (inr ())
  ... | inr p with sumZeroImpliesOperandsZero (binNatToN as) (equalityCommutative p)
  +BIsInherited (zero :: as) (zero :: b) prA prB | inr p | as=0 ,, b=0 rewrite as=0 | b=0 = exFalso ans
    where
      bad : (b : BinNat) → (pr : b ≡ canonical b) → (pr2 : binNatToN b ≡ 0) → b ≡ []
      bad b pr pr2 = transitivity pr (binNatToNZero b pr2)
      t : b ≡ canonical b
      t with canonical b
      t | x :: bl = ::Inj prB
      u : b ≡ []
      u = bad b t b=0
      nono : {A : Set} → {a : A} → {as : List A} → a :: as ≡ [] → False
      nono ()
      ans : False
      ans with inspect (canonical b)
      ans | [] with≡ x rewrite x = nono prB
      ans | (x₁ :: y) with≡ x = nono (transitivity (equalityCommutative x) (transitivity (equalityCommutative t) u))
  +BIsInherited (zero :: as) (one :: b) prA prB rewrite additionNIsCommutative (binNatToN as +N (binNatToN as +N zero)) (succ (binNatToN b +N (binNatToN b +N zero))) | additionNIsCommutative (binNatToN b +N (binNatToN b +N zero)) (binNatToN as +N (binNatToN as +N zero)) | equalityCommutative (productDistributes 2 (binNatToN as) (binNatToN b)) = +BinheritLemma as b (canonicalDescends as prA) (canonicalDescends b prB)
  +BIsInherited (one :: as) (zero :: bs) prA prB rewrite equalityCommutative (productDistributes 2 (binNatToN as) (binNatToN bs)) = +BinheritLemma as bs (canonicalDescends as prA) (canonicalDescends bs prB)
  +BIsInherited (one :: as) (one :: bs) prA prB rewrite additionNIsCommutative (binNatToN as +N (binNatToN as +N zero)) (succ (binNatToN bs +N (binNatToN bs +N zero))) | additionNIsCommutative (binNatToN bs +N (binNatToN bs +N zero)) (2 *N binNatToN as) | equalityCommutative (productDistributes 2 (binNatToN as) (binNatToN bs)) | +BinheritLemma as bs (canonicalDescends as prA) (canonicalDescends bs prB) = refl

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
      t rewrite additionNIsCommutative (succ a) 0 | additionNIsCommutative (succ b) 0 | additionNIsCommutative a (succ a) | additionNIsCommutative b (succ b) = succInjective (succInjective pr)
      u : a +N (a +N zero) ≡ b +N (b +N zero)
      u rewrite additionNIsCommutative a 0 | additionNIsCommutative b 0 = t

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
  binNatToNSucc (one :: n) rewrite additionNIsCommutative (binNatToN n) zero | additionNIsCommutative (binNatToN (incr n)) 0 | binNatToNSucc n = applyEquality succ (additionNIsCommutative (binNatToN n) (succ (binNatToN n)))

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

  parity zero (succ b) pr rewrite additionNIsCommutative b (succ (b +N 0)) = bad pr
    where
      bad : (1 ≡ succ (succ ((b +N 0) +N b))) → False
      bad ()
  parity (succ a) (succ b) pr rewrite additionNIsCommutative b (succ (b +N 0)) | additionNIsCommutative a (succ (a +N 0)) | additionNIsCommutative (a +N 0) a | additionNIsCommutative (b +N 0) b = parity a b (succInjective (succInjective pr))
