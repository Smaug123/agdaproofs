{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Addition
open import Numbers.BinaryNaturals.SubtractionGo
open import Numbers.BinaryNaturals.SubtractionGoPreservesCanonicalRight
open import Numbers.BinaryNaturals.SubtractionGoPreservesCanonicalLeft
open import Orders
open import Semirings.Definition
open import Maybe

module Numbers.BinaryNaturals.Subtraction where

  aMinusAGo : (a : BinNat) → mapMaybe canonical (go zero a a) ≡ yes []
  aMinusAGo [] = refl
  aMinusAGo (zero :: a) with aMinusAGo a
  ... | bl with go zero a a
  aMinusAGo (zero :: a) | bl | yes x rewrite yesInjective bl = refl
  aMinusAGo (one :: a) with aMinusAGo a
  ... | bl with go zero a a
  aMinusAGo (one :: a) | bl | yes x rewrite yesInjective bl = refl

  aMinusALemma : (a : BinNat) → mapMaybe canonical (mapMaybe (_::_ zero) (go zero a a)) ≡ yes []
  aMinusALemma a with inspect (go zero a a)
  aMinusALemma a | no with≡ x with aMinusAGo a
  ... | r rewrite x = exFalso (noNotYes r)
  aMinusALemma a | yes xs with≡ pr with inspect (canonical xs)
  aMinusALemma a | yes xs with≡ pr | [] with≡ pr2 rewrite pr | pr2 = refl
  aMinusALemma a | yes xs with≡ pr | (x :: t) with≡ pr2 with aMinusAGo a
  ... | b rewrite pr | pr2 = exFalso (nonEmptyNotEmpty (yesInjective b))

  aMinusA : (a : BinNat) → mapMaybe canonical (a -B a) ≡ yes []
  aMinusA [] = refl
  aMinusA (zero :: a) = aMinusALemma a
  aMinusA (one :: a) = aMinusALemma a

  goOne : (a b : BinNat) → mapMaybe canonical (go one (incr a) b) ≡ mapMaybe canonical (go zero a b)
  goOne [] [] = refl
  goOne [] (zero :: b) with inspect (go zero [] b)
  goOne [] (zero :: b) | no with≡ pr rewrite pr = refl
  goOne [] (zero :: b) | yes x with≡ pr with goZeroEmpty b pr
  ... | t with inspect (canonical x)
  goOne [] (zero :: b) | yes x with≡ pr | t | [] with≡ pr2 rewrite pr | pr2 = refl
  goOne [] (zero :: b) | yes x with≡ pr | t | (x₁ :: y) with≡ pr2 with goZeroEmpty' b pr
  ... | bl = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative pr2) bl))
  goOne [] (one :: b) with inspect (go one [] b)
  goOne [] (one :: b) | no with≡ pr rewrite pr = refl
  goOne [] (one :: b) | yes x with≡ pr = exFalso (goOneEmpty b pr)
  goOne (zero :: a) [] = refl
  goOne (zero :: a) (zero :: b) = refl
  goOne (zero :: a) (one :: b) = refl
  goOne (one :: a) [] with inspect (go one (incr a) [])
  goOne (one :: a) [] | no with≡ pr with goOne a []
  ... | bl rewrite pr | goEmpty a = exFalso (noNotYes bl)
  goOne (one :: a) [] | yes y with≡ pr with goOne a []
  ... | bl rewrite pr = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity bl (applyEquality (mapMaybe canonical) (goEmpty a))))
  goOne (one :: a) (zero :: b) with inspect (go zero a b)
  goOne (one :: a) (zero :: b) | no with≡ pr with inspect (go one (incr a) b)
  goOne (one :: a) (zero :: b) | no with≡ pr | no with≡ x rewrite pr | x = refl
  goOne (one :: a) (zero :: b) | no with≡ pr | yes y with≡ x with goOne a b
  ... | f rewrite pr | x = exFalso (noNotYes (equalityCommutative f))
  goOne (one :: a) (zero :: b) | yes y with≡ pr with inspect (go one (incr a) b)
  goOne (one :: a) (zero :: b) | yes y with≡ pr | no with≡ x with goOne a b
  ... | f rewrite pr | x = exFalso (noNotYes f)
  goOne (one :: a) (zero :: b) | yes y with≡ pr | yes z with≡ x rewrite pr | x = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative x)) (goOne a b)) (applyEquality (mapMaybe canonical) pr)))
  goOne (one :: a) (one :: b) with inspect (go zero a b)
  goOne (one :: a) (one :: b) | no with≡ pr with inspect (go one (incr a) b)
  goOne (one :: a) (one :: b) | no with≡ pr | no with≡ pr2 rewrite pr | pr2 = refl
  goOne (one :: a) (one :: b) | no with≡ pr | yes x with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr)) (transitivity (equalityCommutative (goOne a b)) (applyEquality (mapMaybe canonical) pr2))))
  goOne (one :: a) (one :: b) | yes y with≡ pr with inspect (go one (incr a) b)
  goOne (one :: a) (one :: b) | yes y with≡ pr | yes z with≡ pr2 rewrite pr | pr2 = applyEquality yes t
    where
      u : canonical z ≡ canonical y
      u = yesInjective (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (goOne a b)) (applyEquality (mapMaybe canonical) pr))
      t : canonical (zero :: z) ≡ canonical (zero :: y)
      t with inspect (canonical z)
      t | [] with≡ pr1 rewrite equalityCommutative u | pr1 = refl
      t | (x :: bl) with≡ pr rewrite equalityCommutative u | pr = refl
  goOne (one :: a) (one :: b) | yes y with≡ pr | no with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goOne a b) (applyEquality (mapMaybe canonical) pr))))

  plusThenMinus : (a b : BinNat) → mapMaybe canonical ((a +B b) -B b) ≡ yes (canonical a)
  plusThenMinus [] b = aMinusA b
  plusThenMinus (zero :: a) [] = refl
  plusThenMinus (zero :: a) (zero :: b) = t
    where
      t : mapMaybe canonical (mapMaybe (zero ::_) (go zero (a +B b) b)) ≡ yes (canonical (zero :: a))
      t with inspect (go zero (a +B b) b)
      t | no with≡ x with plusThenMinus a b
      ... | bl rewrite x = exFalso (noNotYes bl)
      t | yes y with≡ x with plusThenMinus a b
      ... | f rewrite x = applyEquality yes u
        where
          u : canonical (zero :: y) ≡ canonical (zero :: a)
          u with inspect (canonical y)
          u | [] with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
          u | (x :: bl) with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
  plusThenMinus (zero :: a) (one :: b) = t
    where
      t : mapMaybe canonical (mapMaybe (zero ::_) (go zero (a +B b) b)) ≡ yes (canonical (zero :: a))
      t with inspect (go zero (a +B b) b)
      t | no with≡ x with plusThenMinus a b
      ... | bl rewrite x = exFalso (noNotYes bl)
      t | yes y with≡ x with plusThenMinus a b
      ... | f rewrite x = applyEquality yes u
        where
          u : canonical (zero :: y) ≡ canonical (zero :: a)
          u with inspect (canonical y)
          u | [] with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
          u | (x :: bl) with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
  plusThenMinus (one :: a) [] = refl
  plusThenMinus (one :: a) (zero :: b) = t
    where
      t : mapMaybe canonical (mapMaybe (_::_ one) (go zero (a +B b) b)) ≡ yes (one :: canonical a)
      t with inspect (go zero (a +B b) b)
      t | no with≡ x with plusThenMinus a b
      ... | bl rewrite x = exFalso (noNotYes bl)
      t | yes y with≡ x with plusThenMinus a b
      ... | bl rewrite x = applyEquality (λ i → yes (one :: i)) (yesInjective bl)
  plusThenMinus (one :: a) (one :: b) = t
    where
      t : mapMaybe canonical (mapMaybe (_::_ one) (go one (incr (a +B b)) b)) ≡ yes (one :: canonical a)
      t with inspect (go one (incr (a +B b)) b)
      t | no with≡ x with goOne (a +B b) b
      ... | f rewrite x | plusThenMinus a b = exFalso (noNotYes f)
      t | yes y with≡ x with goOne (a +B b) b
      ... | f rewrite x | plusThenMinus a b = applyEquality (λ i → yes (one :: i)) (yesInjective f)

{-

  a+1MinusA : (a : BinNat) → mapMaybe canonical ((incr a) -B a) ≡ yes (one :: [])
  a+1MinusA [] = refl
  a+1MinusA (zero :: a) with inspect (go zero a a)
  a+1MinusA (zero :: a) | no with≡ pr with aMinusAGo a
  ... | r rewrite pr = exFalso (noNotYes r)
  a+1MinusA (zero :: a) | (yes x) with≡ pr with aMinusAGo a
  ... | bl rewrite pr | yesInjective bl = refl
  a+1MinusA (one :: a) with inspect (go one (incr a) a)
  a+1MinusA (one :: a) | no with≡ pr = {!!}
  a+1MinusA (one :: a) | yes x with≡ pr = {!!}

  -Binherited : (a b : ℕ) → (p : (b <N a) || (b ≡ a)) → mapMaybe binNatToN ((NToBinNat a) -B (NToBinNat b)) ≡ yes (subtractionNResult.result (-N p))
  -Binherited a b (inl x) = {!!}
  -Binherited a .a (inr refl) with aMinusA (NToBinNat a)
  ... | t = {!!}

-}
