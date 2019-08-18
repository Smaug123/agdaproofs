{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Functions
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Groups.Definition
open import Numbers.BinaryNaturals.Definition
open import Semirings.Definition

module Numbers.BinaryNaturals.Addition where

-- Define the monoid structure, and show that it's the same as ℕ's

_+Binherit_ : BinNat → BinNat → BinNat
a +Binherit b = NToBinNat (binNatToN a +N binNatToN b)

_+B_ : BinNat → BinNat → BinNat
[] +B b = b
(x :: a) +B [] = x :: a
(zero :: xs) +B (y :: ys) = y :: (xs +B ys)
(one :: xs) +B (zero :: ys) = one :: (xs +B ys)
(one :: xs) +B (one :: ys) = zero :: incr (xs +B ys)

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

-- Show that the monoid structure of ℕ is the same as that of BinNat

+BIsInherited : (a b : BinNat) (prA : a ≡ canonical a) (prB : b ≡ canonical b) → a +Binherit b ≡ a +B b
+BinheritLemma : (a : BinNat) (b : BinNat) (prA : a ≡ canonical a) (prB : b ≡ canonical b) → incr (NToBinNat ((binNatToN a +N binNatToN b) +N ((binNatToN a +N binNatToN b) +N zero))) ≡ one :: (a +B b)

+BIsInherited' : (a b : BinNat) → a +Binherit b ≡ canonical (a +B b)

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
+BIsInherited (x :: a) [] prA _ = transitivity (applyEquality NToBinNat (Semiring.commutative ℕSemiring (binNatToN (x :: a)) 0)) (transitivity (binToBin (x :: a)) (equalityCommutative prA))
+BIsInherited (zero :: as) (zero :: b) prA prB with orderIsTotal 0 (binNatToN as +N binNatToN b)
... | inl (inl 0<) rewrite Semiring.commutative ℕSemiring (binNatToN as) 0 | Semiring.commutative ℕSemiring (binNatToN b) 0 | Semiring.+Associative ℕSemiring (binNatToN as +N binNatToN as) (binNatToN b) (binNatToN b) | equalityCommutative (Semiring.+Associative ℕSemiring (binNatToN as) (binNatToN as) (binNatToN b)) | Semiring.commutative ℕSemiring (binNatToN as) (binNatToN b) | Semiring.+Associative ℕSemiring (binNatToN as) (binNatToN b) (binNatToN as) | equalityCommutative (Semiring.+Associative ℕSemiring (binNatToN as +N binNatToN b) (binNatToN as) (binNatToN b)) | Semiring.commutative ℕSemiring 0 ((binNatToN as +N binNatToN b) +N (binNatToN as +N binNatToN b)) | equalityCommutative (Semiring.+Associative ℕSemiring (binNatToN as +N binNatToN b) (binNatToN as +N binNatToN b) 0) = transitivity (doubleIsBitShift (binNatToN as +N binNatToN b) (identityOfIndiscernablesRight _ _ _ _<N_ 0< (Semiring.commutative ℕSemiring (binNatToN b) _))) (applyEquality (zero ::_) (+BIsInherited as b (canonicalDescends as prA) (canonicalDescends b prB)))
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
+BIsInherited (zero :: as) (one :: b) prA prB rewrite Semiring.commutative ℕSemiring (binNatToN as +N (binNatToN as +N zero)) (succ (binNatToN b +N (binNatToN b +N zero))) | Semiring.commutative ℕSemiring (binNatToN b +N (binNatToN b +N zero)) (binNatToN as +N (binNatToN as +N zero)) | equalityCommutative (Semiring.+DistributesOver* ℕSemiring 2 (binNatToN as) (binNatToN b)) = +BinheritLemma as b (canonicalDescends as prA) (canonicalDescends b prB)
+BIsInherited (one :: as) (zero :: bs) prA prB rewrite equalityCommutative (Semiring.+DistributesOver* ℕSemiring 2 (binNatToN as) (binNatToN bs)) = +BinheritLemma as bs (canonicalDescends as prA) (canonicalDescends bs prB)
+BIsInherited (one :: as) (one :: bs) prA prB rewrite Semiring.commutative ℕSemiring (binNatToN as +N (binNatToN as +N zero)) (succ (binNatToN bs +N (binNatToN bs +N zero))) | Semiring.commutative ℕSemiring (binNatToN bs +N (binNatToN bs +N zero)) (2 *N binNatToN as) | equalityCommutative (Semiring.+DistributesOver* ℕSemiring 2 (binNatToN as) (binNatToN bs)) | +BinheritLemma as bs (canonicalDescends as prA) (canonicalDescends bs prB) = refl

+BIsInherited'[] : (b : BinNat) → [] +Binherit b ≡ canonical ([] +B b)
+BIsInherited'[] [] = refl
+BIsInherited'[] (zero :: b) with inspect (canonical b)
+BIsInherited'[] (zero :: b) | [] with≡ pr rewrite binNatToNZero' b pr | pr = refl
+BIsInherited'[] (zero :: b) | (x :: bl) with≡ pr rewrite pr = ans
  where
    contr : {a : _} {A : Set a} {l1 l2 : List A} → {x : A} → l1 ≡ [] → l1 ≡ x :: l2 → False
    contr {l1 = []} p1 ()
    contr {l1 = x :: l1} () p2
    ans : NToBinNat (binNatToN b +N (binNatToN b +N zero)) ≡ zero :: x :: bl
    ans with inspect (binNatToN b)
    ans | zero with≡ th rewrite th = exFalso (contr (binNatToNZero b th) pr)
    ans | succ th with≡ blah rewrite blah | doubleIsBitShift' th = applyEquality (zero ::_) (transitivity (equalityCommutative u) pr)
      where
        u : canonical b ≡ incr (NToBinNat th)
        u = transitivity (equalityCommutative (binToBin b)) (applyEquality NToBinNat blah)
+BIsInherited'[] (one :: b) with inspect (binNatToN b)
... | zero with≡ pr rewrite pr = applyEquality (one ::_) (equalityCommutative (binNatToNZero b pr))
... | (succ bl) with≡ pr = ans
  where
    u : NToBinNat (2 *N binNatToN b) ≡ zero :: canonical b
    u with doubleIsBitShift' bl
    ... | t = transitivity (identityOfIndiscernablesLeft _ _ _ _≡_ t (applyEquality (λ i → NToBinNat (2 *N i)) (equalityCommutative pr))) (applyEquality (zero ::_) (transitivity (applyEquality NToBinNat (equalityCommutative pr)) (binToBin b)))
    ans : incr (NToBinNat (binNatToN b +N (binNatToN b +N zero))) ≡ one :: canonical b
    ans = applyEquality incr u

+BIsInherited' [] b = +BIsInherited'[] b
+BIsInherited' (zero :: a) [] with inspect (binNatToN a)
+BIsInherited' (zero :: a) [] | zero with≡ x rewrite x | binNatToNZero a x = refl
+BIsInherited' (zero :: a) [] | succ y with≡ x rewrite x | Semiring.commutative ℕSemiring (y +N succ (y +N 0)) 0 = transitivity (doubleIsBitShift' y) (transitivity (applyEquality (λ i → (zero :: NToBinNat i)) (equalityCommutative x)) (transitivity (applyEquality (λ i → zero :: i) (binToBin a)) (canonicalAscends' {zero} a bad)))
  where
    bad : canonical a ≡ [] → False
    bad pr with transitivity (equalityCommutative x) (transitivity (equalityCommutative (binNatToNIsCanonical a)) (applyEquality binNatToN pr))
    bad pr | ()
+BIsInherited' (one :: a) [] with inspect (binNatToN a)
+BIsInherited' (one :: a) [] | 0 with≡ x rewrite x | binNatToNZero a x = refl
+BIsInherited' (one :: a) [] | succ n with≡ x rewrite x | doubleIsBitShift' n = applyEquality incr {_} {zero :: canonical a} (transitivity {x = _} {NToBinNat (2 *N succ n)} bl (transitivity (doubleIsBitShift' n) (applyEquality (zero ::_) (transitivity (applyEquality NToBinNat (equalityCommutative x)) (binToBin a)))))
  where
    bl : incr (NToBinNat ((n +N succ (n +N 0)) +N 0)) ≡ NToBinNat (succ (n +N succ (n +N 0)))
    bl rewrite equalityCommutative x | Semiring.commutative ℕSemiring (n +N succ (n +N 0)) 0 = refl
+BIsInherited' (zero :: as) (zero :: bs) rewrite equalityCommutative (Semiring.+DistributesOver* ℕSemiring 2 (binNatToN as) (binNatToN bs)) = ans
  where
    ans : NToBinNat (2 *N (binNatToN as +N binNatToN bs)) ≡ canonical (zero :: (as +B bs))
    ans with inspect (binNatToN as +N binNatToN bs)
    ans | zero with≡ x with sumZeroImpliesOperandsZero (binNatToN as) x
    ... | as=0 ,, bs=0 rewrite as=0 | bs=0 = foo
      where
        u : canonical (as +Binherit bs) ≡ []
        u rewrite as=0 | bs=0 = refl
        foo : [] ≡ canonical (zero :: (as +B bs))
        foo = transitivity (transitivity b (applyEquality (λ i → canonical (zero :: i)) (+BIsInherited' as bs))) (canonicalAscends'' {zero} (as +B bs))
          where
            b : [] ≡ canonical (zero :: (as +Binherit bs))
            b rewrite u = refl
    ans | succ y with≡ x rewrite x | doubleIsBitShift' y = transitivity (applyEquality (λ i → zero :: NToBinNat i) (equalityCommutative x)) ans2
      where
        u : 0 <N binNatToN (as +B bs)
        u rewrite equalityCommutative (binNatToNIsCanonical (as +B bs)) | equalityCommutative (+BIsInherited' as bs) | x | nToN (succ y) = succIsPositive y
        ans2 : zero :: NToBinNat (binNatToN as +N binNatToN bs) ≡ canonical (zero :: (as +B bs))
        ans2 rewrite +BIsInherited' as bs = canonicalAscends (as +B bs) u
+BIsInherited' (zero :: as) (one :: bs) rewrite Semiring.commutative ℕSemiring (2 *N binNatToN as) (succ (2 *N binNatToN bs)) | Semiring.commutative ℕSemiring (2 *N binNatToN bs) (2 *N binNatToN as) | equalityCommutative (Semiring.+DistributesOver* ℕSemiring 2 (binNatToN as) (binNatToN bs)) = ans2
  where
    ans2 : incr (NToBinNat (2 *N (binNatToN as +N binNatToN bs))) ≡ one :: canonical (as +B bs)
    ans2 with inspect (binNatToN as +N binNatToN bs)
    ans2 | zero with≡ x with sumZeroImpliesOperandsZero (binNatToN as) x
    ans2 | zero with≡ x | as=0 ,, bs=0 rewrite as=0 | bs=0 = applyEquality (one ::_) (transitivity t (+BIsInherited' as bs))
      where
        t : [] ≡ as +Binherit bs
        t rewrite as=0 | bs=0 = refl
    ans2 | succ y with≡ x rewrite x | doubleIsBitShift' y = applyEquality (one ::_) (transitivity (applyEquality NToBinNat (equalityCommutative x)) (+BIsInherited' as bs))
+BIsInherited' (one :: as) (zero :: bs) rewrite equalityCommutative (Semiring.+DistributesOver* ℕSemiring 2 (binNatToN as) (binNatToN bs)) = ans
  where
    ans : incr (NToBinNat (2 *N (binNatToN as +N binNatToN bs))) ≡ one :: canonical (as +B bs)
    ans with inspect (binNatToN as +N binNatToN bs)
    ans | zero with≡ x with sumZeroImpliesOperandsZero (binNatToN as) x
    ... | as=0 ,, bs=0 rewrite as=0 | bs=0 = applyEquality (one ::_) (transitivity t (+BIsInherited' as bs))
      where
        t : [] ≡ NToBinNat (binNatToN as +N binNatToN bs)
        t rewrite as=0 | bs=0 = refl
    ans | succ y with≡ x rewrite x | doubleIsBitShift' y = applyEquality (one ::_) (transitivity (applyEquality NToBinNat (equalityCommutative x)) (+BIsInherited' as bs))
+BIsInherited' (one :: as) (one :: bs) rewrite Semiring.commutative ℕSemiring (2 *N binNatToN as) (succ (2 *N binNatToN bs)) | Semiring.commutative ℕSemiring (2 *N binNatToN bs) (2 *N binNatToN as) | equalityCommutative (Semiring.+DistributesOver* ℕSemiring 2 (binNatToN as) (binNatToN bs)) = ans
  where
    ans : incr (incr (NToBinNat (2 *N (binNatToN as +N binNatToN bs)))) ≡ canonical (zero :: incr (as +B bs))
    ans with inspect (binNatToN as +N binNatToN bs)
    ... | zero with≡ x with sumZeroImpliesOperandsZero (binNatToN as) x
    ans | zero with≡ x | as=0 ,, bs=0 rewrite as=0 | bs=0 = bar
      where
        u' : canonical (as +Binherit bs) ≡ []
        u' rewrite as=0 | bs=0 = refl
        u : canonical (as +B bs) ≡ []
        u rewrite equalityCommutative (+BIsInherited' as bs) = transitivity (NToBinNatIsCanonical (binNatToN as +N binNatToN bs)) u'
        t : canonical (incr (as +B bs)) ≡ one :: []
        t rewrite incrPreservesCanonical' (as +B bs) | u = refl
        bar : zero :: one :: [] ≡ canonical (zero :: incr (as +B bs))
        bar rewrite t = refl
    ans | succ y with≡ x rewrite x | doubleIsBitShift' y = transitivity (applyEquality (λ i → zero :: incr (NToBinNat i)) (equalityCommutative x)) ans2
      where
        ans2 : zero :: incr (as +Binherit bs) ≡ canonical (zero :: incr (as +B bs))
        ans2 rewrite +BIsInherited' as bs | equalityCommutative (incrPreservesCanonical' (as +B bs)) | canonicalAscends' {zero} (incr (as +B bs)) (incrNonzero (as +B bs)) = refl
