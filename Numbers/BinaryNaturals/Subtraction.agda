{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Numbers.BinaryNaturals.Definition
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

{-
  goOne : (a b : BinNat) → mapMaybe canonical (go one (incr a) b) ≡ mapMaybe canonical (go zero a b)
  goOne [] [] = refl
  goOne [] (zero :: b) with inspect (go zero [] b)
  goOne [] (zero :: b) | no with≡ pr = {!!}
  goOne [] (zero :: b) | yes x with≡ pr with goZeroEmpty b pr
  ... | t = {!!}
  goOne [] (one :: b) with inspect (go one [] b)
  goOne [] (one :: b) | no with≡ pr rewrite pr = refl
  goOne [] (one :: b) | yes x with≡ pr = exFalso (goOneEmpty b pr)
  goOne (x :: a) b = {!!}

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
