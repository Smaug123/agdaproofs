{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Functions
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Groups.Definition
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Addition
open import Semirings.Definition

module Numbers.BinaryNaturals.Multiplication where

  _*Binherit_ : BinNat → BinNat → BinNat
  a *Binherit b = NToBinNat (binNatToN a *N binNatToN b)

  _*B_ : BinNat → BinNat → BinNat
  [] *B b = []
  (zero :: a) *B b = zero :: (a *B b)
  (one :: a) *B b = (zero :: (a *B b)) +B b

  contr : {a : _} {A : Set a} {l1 l2 : List A} → {x : A} → l1 ≡ [] → l1 ≡ x :: l2 → False
  contr {l1 = []} p1 ()
  contr {l1 = x :: l1} () p2

  *BEmpty : (a : BinNat) → canonical (a *B []) ≡ []
  *BEmpty [] = refl
  *BEmpty (zero :: a) rewrite *BEmpty a = refl
  *BEmpty (one :: a) rewrite *BEmpty a = refl

  canonicalDistributesPlus : (a b : BinNat) → canonical (a +B b) ≡ canonical a +B canonical b
  canonicalDistributesPlus a b = transitivity ans (+BIsInherited (canonical a) (canonical b) (canonicalIdempotent a) (canonicalIdempotent b))
    where
      ans : canonical (a +B b) ≡ NToBinNat (binNatToN (canonical a) +N binNatToN (canonical b))
      ans rewrite binNatToNIsCanonical a | binNatToNIsCanonical b = equalityCommutative (+BIsInherited' a b)

  incrPullsOut : (a b : BinNat) → incr (a +B b) ≡ (incr a) +B b
  incrPullsOut [] [] = refl
  incrPullsOut [] (zero :: b) = refl
  incrPullsOut [] (one :: b) = refl
  incrPullsOut (zero :: a) [] = refl
  incrPullsOut (zero :: a) (zero :: b) = refl
  incrPullsOut (zero :: a) (one :: b) = refl
  incrPullsOut (one :: a) [] = refl
  incrPullsOut (one :: a) (zero :: b) = applyEquality (zero ::_) (incrPullsOut a b)
  incrPullsOut (one :: a) (one :: b) = applyEquality (one ::_) (incrPullsOut a b)

  timesZero : (a b : BinNat) → canonical a ≡ [] → canonical (a *B b) ≡ []
  timesZero [] b pr = refl
  timesZero (zero :: a) b pr with inspect (canonical a)
  timesZero (zero :: a) b pr | [] with≡ prA rewrite prA | timesZero a b prA = refl
  timesZero (zero :: a) b pr | (a1 :: as) with≡ prA rewrite prA = exFalso (nonEmptyNotEmpty pr)

  timesZero'' : (a b : BinNat) → canonical (a *B b) ≡ [] → (canonical a ≡ []) || (canonical b ≡ [])
  timesZero'' [] b pr = inl refl
  timesZero'' (x :: a) [] pr = inr refl
  timesZero'' (zero :: as) (zero :: bs) pr with inspect (canonical as)
  timesZero'' (zero :: as) (zero :: bs) pr | y with≡ x with inspect (canonical bs)
  timesZero'' (zero :: as) (zero :: bs) pr | [] with≡ prAs | y₁ with≡ prBs rewrite prAs = inl refl
  timesZero'' (zero :: as) (zero :: bs) pr | (a1 :: a's) with≡ prAs | [] with≡ prBs rewrite prBs = inr refl
  timesZero'' (zero :: as) (zero :: bs) pr | (a1 :: a's) with≡ prAs | (x :: y) with≡ prBs with inspect (canonical (as *B (zero :: bs)))
  timesZero'' (zero :: as) (zero :: bs) pr | (a1 :: a's) with≡ prAs | (b1 :: b's) with≡ prBs | [] with≡ pr' with timesZero'' as (zero :: bs) pr'
  timesZero'' (zero :: as) (zero :: bs) pr | (a1 :: a's) with≡ prAs | (b1 :: b's) with≡ prBs | [] with≡ pr' | inl x rewrite prAs | prBs | pr' | x = exFalso (nonEmptyNotEmpty x)
  timesZero'' (zero :: as) (zero :: bs) pr | (a1 :: a's) with≡ prAs | (b1 :: b's) with≡ prBs | [] with≡ pr' | inr x rewrite prBs | pr' | x = exFalso (nonEmptyNotEmpty x)
  timesZero'' (zero :: as) (zero :: bs) pr | (a1 :: a's) with≡ prAs | (b1 :: b's) with≡ prBs | (x :: y) with≡ pr' rewrite prAs | prBs | pr' = exFalso (nonEmptyNotEmpty pr)
  timesZero'' (zero :: as) (one :: bs) pr with inspect (canonical as)
  timesZero'' (zero :: as) (one :: bs) pr | [] with≡ x rewrite x = inl refl
  timesZero'' (zero :: as) (one :: bs) pr | (a1 :: a's) with≡ x with inspect (canonical (as *B (one :: bs)))
  timesZero'' (zero :: as) (one :: bs) pr | (a1 :: a's) with≡ x | [] with≡ pr' with timesZero'' as (one :: bs) pr'
  timesZero'' (zero :: as) (one :: bs) pr | (a1 :: a's) with≡ x | [] with≡ pr' | inl pr'' rewrite x | pr' | pr'' = exFalso (nonEmptyNotEmpty pr'')
  timesZero'' (zero :: as) (one :: bs) pr | (a1 :: a's) with≡ x | (x₁ :: y) with≡ pr' rewrite x | pr' = exFalso (nonEmptyNotEmpty pr)
  timesZero'' (one :: as) (zero :: bs) pr with inspect (canonical bs)
  timesZero'' (one :: as) (zero :: bs) pr | [] with≡ x rewrite x = inr refl
  timesZero'' (one :: as) (zero :: bs) pr | (b1 :: b's) with≡ prB with inspect (canonical ((as *B (zero :: bs)) +B bs))
  timesZero'' (one :: as) (zero :: bs) pr | (b1 :: b's) with≡ prB | [] with≡ x rewrite equalityCommutative (+BIsInherited' (as *B (zero :: bs)) bs) = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative prB) v))
    where
      t : binNatToN (as *B (zero :: bs)) +N binNatToN bs ≡ 0
      t = transitivity (equalityCommutative (nToN _)) (applyEquality binNatToN x)
      u : (binNatToN (as *B (zero :: bs)) ≡ 0) && (binNatToN bs ≡ 0)
      u = sumZeroImpliesOperandsZero _ t
      v : canonical bs ≡ []
      v with u
      ... | fst ,, snd = binNatToNZero bs snd
  timesZero'' (one :: as) (zero :: bs) pr | (b1 :: b's) with≡ prB | (x₁ :: y) with≡ x rewrite prB | x = exFalso (nonEmptyNotEmpty pr)

  lemma : {i : Bit} → (a b : BinNat) → canonical a ≡ canonical b → canonical (i :: a) ≡ canonical (i :: b)
  lemma {zero} a b pr with inspect (canonical a)
  lemma {zero} a b pr | [] with≡ x rewrite x | equalityCommutative pr = refl
  lemma {zero} a b pr | (a1 :: as) with≡ x rewrite x | equalityCommutative pr = refl
  lemma {one} a b pr = applyEquality (one ::_) pr

  binNatToNDistributesPlus : (a b : BinNat) → binNatToN (a +B b) ≡ binNatToN a +N binNatToN b
  binNatToNDistributesPlus a b = transitivity (equalityCommutative (binNatToNIsCanonical (a +B b))) (transitivity (applyEquality binNatToN (equalityCommutative (+BIsInherited' a b))) (nToN (binNatToN a +N binNatToN b)))

  +BAssociative : (a b c : BinNat) → canonical (a +B (b +B c)) ≡ canonical ((a +B b) +B c)
  +BAssociative a b c rewrite equalityCommutative (+BIsInherited' a (b +B c)) | equalityCommutative (+BIsInherited' (a +B b) c) | binNatToNDistributesPlus a b | binNatToNDistributesPlus b c | equalityCommutative (Semiring.+Associative ℕSemiring (binNatToN a) (binNatToN b) (binNatToN c)) = refl

  timesOne : (a b : BinNat) → (canonical b) ≡ (one :: []) → canonical (a *B b) ≡ canonical a
  timesOne [] b pr = refl
  timesOne (zero :: a) b pr with inspect (canonical (a *B b))
  timesOne (zero :: a) b pr | [] with≡ prAB with timesZero'' a b prAB
  timesOne (zero :: a) b pr | [] with≡ prAB | inl a=0 rewrite a=0 | prAB = refl
  timesOne (zero :: a) b pr | [] with≡ prAB | inr b=0 = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative pr) b=0))
  timesOne (zero :: a) b pr | (ab1 :: abs) with≡ prAB with inspect (canonical a)
  timesOne (zero :: a) b pr | (ab1 :: abs) with≡ prAB | [] with≡ x = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative prAB) (timesZero a b x)))
  timesOne (zero :: a) b pr | (ab1 :: abs) with≡ prAB | (x₁ :: y) with≡ x rewrite prAB | x | timesOne a b pr = applyEquality (zero ::_) (transitivity (equalityCommutative prAB) x)
  timesOne (one :: a) (zero :: b) pr with canonical b
  timesOne (one :: a) (zero :: b) () | []
  timesOne (one :: a) (zero :: b) () | x :: bl
  timesOne (one :: a) (one :: b) pr rewrite canonicalDistributesPlus (a *B (one :: b)) b | ::Inj pr | +BCommutative (canonical (a *B (one :: b))) [] | timesOne a (one :: b) pr = refl

  timesZero' : (a b : BinNat) → canonical b ≡ [] → canonical (a *B b) ≡ []
  timesZero' [] b pr = refl
  timesZero' (zero :: a) b pr with inspect (canonical (a *B b))
  timesZero' (zero :: a) b pr | [] with≡ x rewrite x = refl
  timesZero' (zero :: a) b pr | (ab1 :: abs) with≡ prAB rewrite prAB = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative prAB) (timesZero' a b pr)))
  timesZero' (one :: a) b pr rewrite canonicalDistributesPlus (zero :: (a *B b)) b | pr | +BCommutative (canonical (zero :: (a *B b))) [] = ans
    where
      ans : canonical (zero :: (a *B b)) ≡ []
      ans with inspect (canonical (a *B b))
      ans | [] with≡ x rewrite x = refl
      ans | (x₁ :: y) with≡ x rewrite x = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative x) (timesZero' a b pr)))

  canonicalDistributesTimes : (a b : BinNat) → canonical (a *B b) ≡ canonical ((canonical a) *B (canonical b))
  canonicalDistributesTimes [] b = refl
  canonicalDistributesTimes (zero :: a) b with inspect (canonical a)
  canonicalDistributesTimes (zero :: a) b | [] with≡ x rewrite timesZero a b x | x = refl
  canonicalDistributesTimes (zero :: a) b | (a1 :: as) with≡ prA with inspect (canonical b)
  canonicalDistributesTimes (zero :: a) b | (a1 :: as) with≡ prA | [] with≡ prB rewrite prA | prB = ans
    where
      ans : canonical (zero :: (a *B b)) ≡ canonical (zero :: ((a1 :: as) *B []))
      ans with inspect (canonical ((a1 :: as) *B []))
      ans | [] with≡ x rewrite x | timesZero' a b prB = refl
      ans | (x₁ :: y) with≡ x = exFalso (nonEmptyNotEmpty (equalityCommutative (transitivity (equalityCommutative (timesZero' (a1 :: as) [] refl)) x)))
  canonicalDistributesTimes (zero :: a) b | (a1 :: as) with≡ prA | (b1 :: bs) with≡ prB with inspect (canonical (a *B b))
  canonicalDistributesTimes (zero :: a) b | (a1 :: as) with≡ prA | (b1 :: bs) with≡ prB | [] with≡ x with timesZero'' a b x
  canonicalDistributesTimes (zero :: a) b | (a1 :: as) with≡ prA | (b1 :: bs) with≡ prB | [] with≡ x | inl a=0 = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative prA) a=0))
  canonicalDistributesTimes (zero :: a) b | (a1 :: as) with≡ prA | (b1 :: bs) with≡ prB | [] with≡ x | inr b=0 = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative prB) b=0))
  canonicalDistributesTimes (zero :: a) b | (a1 :: as) with≡ prA | (b1 :: bs) with≡ prB | (ab1 :: abs) with≡ x rewrite prA | prB | x = ans
    where
      ans : zero :: ab1 :: abs ≡ canonical (zero :: ((a1 :: as) *B (b1 :: bs)))
      ans rewrite equalityCommutative prA | equalityCommutative prB | equalityCommutative (canonicalDistributesTimes a b) | x = refl
  canonicalDistributesTimes (one :: a) b = transitivity (canonicalDistributesPlus (zero :: (a *B b)) b) (transitivity (transitivity (applyEquality (_+B canonical b) (transitivity (equalityCommutative (canonicalAscends'' (a *B b))) (transitivity (applyEquality (λ i → canonical (zero :: i)) (canonicalDistributesTimes a b)) (canonicalAscends'' (canonical a *B canonical b))))) (applyEquality (λ i → canonical (zero :: (canonical a *B canonical b)) +B i) (canonicalIdempotent b))) (equalityCommutative (canonicalDistributesPlus (zero :: (canonical a *B canonical b)) (canonical b))))

  NToBinNatDistributesPlus : (a b : ℕ) → NToBinNat (a +N b) ≡ NToBinNat a +B NToBinNat b
  NToBinNatDistributesPlus zero b = refl
  NToBinNatDistributesPlus (succ a) b with inspect (NToBinNat a)
  ... | bl with≡ prA with inspect (NToBinNat (a +N b))
  ... | q with≡ prAB = transitivity (applyEquality incr (NToBinNatDistributesPlus a b)) (incrPullsOut (NToBinNat a) (NToBinNat b))

  timesCommutative : (a b : BinNat) → canonical (a *B b) ≡ canonical (b *B a)
  timesCommLemma : (a b : BinNat) → canonical (zero :: (b *B a)) ≡ canonical (b *B (zero :: a))
  timesCommLemma a b rewrite timesCommutative b (zero :: a) | equalityCommutative (canonicalAscends'' {zero} (b *B a)) | equalityCommutative (canonicalAscends'' {zero} (a *B b)) | timesCommutative b a = refl

  timesCommutative [] b rewrite timesZero' b [] refl = refl
  timesCommutative (x :: a) [] rewrite timesZero' (x :: a) [] refl = refl
  timesCommutative (zero :: as) (zero :: b) rewrite equalityCommutative (canonicalAscends'' {zero} (as *B (zero :: b))) | timesCommutative as (zero :: b) | canonicalAscends'' {zero} (zero :: b *B as) | equalityCommutative (canonicalAscends'' {zero} (b *B (zero :: as))) | timesCommutative b (zero :: as) | canonicalAscends'' {zero} (zero :: (as *B b)) = ans
    where
      ans : canonical (zero :: zero :: (b *B as)) ≡ canonical (zero :: zero :: (as *B b))
      ans rewrite equalityCommutative (canonicalAscends'' {zero} (zero :: (b *B as))) | equalityCommutative (canonicalAscends'' {zero} (b *B as)) | timesCommutative b as | canonicalAscends'' {zero} (as *B b) | canonicalAscends'' {zero} (zero :: (as *B b)) = refl
  timesCommutative (zero :: as) (one :: b) = transitivity (equalityCommutative (canonicalAscends'' (as *B (one :: b)))) (transitivity (applyEquality (λ i → canonical (zero :: i)) (timesCommutative as (one :: b))) (transitivity (applyEquality (λ i → canonical (zero :: i)) ans) (canonicalAscends'' ((b *B (zero :: as)) +B as))))
    where
      ans : canonical ((zero :: (b *B as)) +B as) ≡ canonical ((b *B (zero :: as)) +B as)
      ans rewrite canonicalDistributesPlus (zero :: (b *B as)) as | canonicalDistributesPlus (b *B (zero :: as)) as = applyEquality (_+B canonical as) (timesCommLemma as b)
  timesCommutative (one :: as) (zero :: bs) = transitivity (equalityCommutative (canonicalAscends'' ((as *B (zero :: bs)) +B bs))) (transitivity (applyEquality (λ i → canonical (zero :: i)) ans) (canonicalAscends'' (bs *B (one :: as))))
    where
      ans : canonical ((as *B (zero :: bs)) +B bs) ≡ canonical (bs *B (one :: as))
      ans rewrite timesCommutative bs (one :: as) | canonicalDistributesPlus (as *B (zero :: bs)) bs | canonicalDistributesPlus (zero :: (as *B bs)) bs = applyEquality (_+B canonical bs) (equalityCommutative (timesCommLemma bs as))
  timesCommutative (one :: as) (one :: bs) = applyEquality (one ::_) (transitivity (canonicalDistributesPlus (as *B (one :: bs)) bs) (transitivity (transitivity (applyEquality (_+B canonical bs) (timesCommutative as (one :: bs))) (transitivity ans (equalityCommutative (applyEquality (_+B canonical as) (timesCommutative bs (one :: as)))))) (equalityCommutative (canonicalDistributesPlus (bs *B (one :: as)) as))))
    where
      ans : canonical ((zero :: (bs *B as)) +B as) +B canonical bs ≡ canonical ((zero :: (as *B bs)) +B bs) +B canonical as
      ans rewrite equalityCommutative (canonicalDistributesPlus ((zero :: (bs *B as)) +B as) bs) | equalityCommutative (canonicalDistributesPlus ((zero :: (as *B bs)) +B bs) as) | equalityCommutative (+BAssociative (zero :: (bs *B as)) as bs) | equalityCommutative (+BAssociative (zero :: (as *B bs)) bs as) | canonicalDistributesPlus (zero :: (bs *B as)) (as +B bs) | canonicalDistributesPlus (zero :: (as *B bs)) (bs +B as) | equalityCommutative (canonicalAscends'' {zero} (bs *B as)) | timesCommutative bs as | canonicalAscends'' {zero} (as *B bs) | +BCommutative as bs = refl

  *BIsInherited : (a b : BinNat) → a *Binherit b ≡ canonical (a *B b)
  *BIsInherited a b = transitivity (applyEquality NToBinNat t) (transitivity (binToBin (canonical (a *B b))) (equalityCommutative (canonicalIdempotent (a *B b))))
    where
      ans : (a b : BinNat) → binNatToN a *N binNatToN b ≡ binNatToN (a *B b)
      ans [] b = refl
      ans (zero :: a) b rewrite equalityCommutative (ans a b) = equalityCommutative (Semiring.*Associative ℕSemiring 2 (binNatToN a) (binNatToN b))
      ans (one :: a) b rewrite binNatToNDistributesPlus (zero :: (a *B b)) b | Semiring.commutative ℕSemiring (binNatToN b) ((2 *N (binNatToN a)) *N (binNatToN b)) | equalityCommutative (ans a b) = applyEquality (_+N binNatToN b) (equalityCommutative (Semiring.*Associative ℕSemiring 2 (binNatToN a) (binNatToN b)))
      t : (binNatToN a *N binNatToN b) ≡ binNatToN (canonical (a *B b))
      t = transitivity (ans a b) (equalityCommutative (binNatToNIsCanonical (a *B b)))
