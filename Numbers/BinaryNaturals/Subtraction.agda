{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Functions
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Groups.Definition
open import Numbers.BinaryNaturals.Definition
open import Orders
open import Semirings.Definition
open import Maybe

module Numbers.BinaryNaturals.Subtraction where

  decr : BinNat → Maybe BinNat
  decr [] = no
  decr (zero :: xs) with decr xs
  decr (zero :: xs) | no = no
  decr (zero :: xs) | yes x = yes (one :: x)
  decr (one :: xs) = yes (zero :: xs)

  go : Bit → BinNat → BinNat → Maybe BinNat
  go zero [] [] = yes []
  go one [] [] = no
  go zero [] (zero :: b) = go zero [] b
  go zero [] (one :: b) = no
  go one [] (x :: b) = no
  go zero (zero :: a) [] = yes (zero :: a)
  go one (zero :: a) [] = mapMaybe (one ::_) (go one a [])
  go zero (zero :: a) (zero :: b) = mapMaybe (zero ::_) (go zero a b)
  go one (zero :: a) (zero :: b) = mapMaybe (one ::_) (go one a b)
  go zero (zero :: a) (one :: b) = mapMaybe (one ::_) (go one a b)
  go one (zero :: a) (one :: b) = mapMaybe (zero ::_) (go one a b)
  go zero (one :: a) [] = yes (one :: a)
  go zero (one :: a) (zero :: b) = mapMaybe (one ::_) (go zero a b)
  go zero (one :: a) (one :: b) = mapMaybe (zero ::_) (go zero a b)
  go one (one :: a) [] = yes (zero :: a)
  go one (one :: a) (zero :: b) = mapMaybe (zero ::_) (go zero a b)
  go one (one :: a) (one :: b) = mapMaybe (one ::_) (go one a b)

  _-B_ : BinNat → BinNat → Maybe BinNat
  a -B b = go zero a b

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

  canonicalRespectsGoFirst : (bit : Bit) (a b : BinNat) → mapMaybe canonical (go bit a b) ≡ mapMaybe canonical (go bit (canonical a) b)
  canonicalRespectsGoFirst zero [] b = refl
  canonicalRespectsGoFirst zero (zero :: a) [] = {!!}
  canonicalRespectsGoFirst zero (zero :: a) (zero :: b) with canonicalRespectsGoFirst zero a b
  ... | bl with inspect (go zero a b)
  canonicalRespectsGoFirst zero (zero :: a) (zero :: b) | bl | no with≡ pr with canonical a
  canonicalRespectsGoFirst zero (zero :: a) (zero :: b) | bl | no with≡ pr | [] rewrite pr = bl
  canonicalRespectsGoFirst zero (zero :: a) (zero :: b) | bl | no with≡ pr | x :: can rewrite pr | mapMaybePreservesNo canonical (go zero (x :: can) b) (equalityCommutative bl) = refl
  canonicalRespectsGoFirst zero (zero :: a) (zero :: b) | bl | yes x with≡ pr with canonical a
  canonicalRespectsGoFirst zero (zero :: a) (zero :: b) | bl | yes x with≡ pr | [] rewrite pr | equalityCommutative bl = {!!}
  canonicalRespectsGoFirst zero (zero :: a) (zero :: b) | bl | yes x with≡ pr | x₁ :: as = {!!}
  canonicalRespectsGoFirst zero (zero :: a) (one :: b) = {!!}
  canonicalRespectsGoFirst zero (one :: a) b = {!!}
  canonicalRespectsGoFirst one a b = {!!}

  -Binherited : (a b : ℕ) → (p : (b <N a) || (b ≡ a)) → mapMaybe binNatToN ((NToBinNat a) -B (NToBinNat b)) ≡ yes (subtractionNResult.result (-N p))
  -Binherited a b (inl x) = {!!}
  -Binherited a .a (inr refl) with aMinusA (NToBinNat a)
  ... | t = {!!}
