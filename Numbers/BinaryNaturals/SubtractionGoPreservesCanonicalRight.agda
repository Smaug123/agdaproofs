{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Numbers.BinaryNaturals.Definition
open import Maybe
open import Numbers.BinaryNaturals.SubtractionGo

module Numbers.BinaryNaturals.SubtractionGoPreservesCanonicalRight where

goPreservesCanonicalRightZero : (a b : BinNat) → mapMaybe canonical (go zero a b) ≡ mapMaybe canonical (go zero a (canonical b))
goPreservesCanonicalRightOne : (a b : BinNat) → mapMaybe canonical (go one a b) ≡ mapMaybe canonical (go one a (canonical b))

goPreservesCanonicalRightZero [] [] = refl
goPreservesCanonicalRightZero [] (zero :: b) with inspect (go zero [] b)
goPreservesCanonicalRightZero [] (zero :: b) | no with≡ pr with inspect (canonical b)
goPreservesCanonicalRightZero [] (zero :: b) | no with≡ pr | [] with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (transitivity (goPreservesCanonicalRightZero [] b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero [] i)) pr2) refl))))
goPreservesCanonicalRightZero [] (zero :: b) | no with≡ pr | (x :: y) with≡ pr2 with inspect (go zero [] (x :: y))
goPreservesCanonicalRightZero [] (zero :: b) | no with≡ pr | (x :: y) with≡ pr2 | no with≡ pr3 rewrite pr | pr2 | pr3 = refl
goPreservesCanonicalRightZero [] (zero :: b) | no with≡ pr | (x :: y) with≡ pr2 | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (transitivity (goPreservesCanonicalRightZero [] b) (applyEquality (mapMaybe canonical) pr3))))
goPreservesCanonicalRightZero [] (zero :: b) | yes r with≡ pr with inspect (canonical b)
goPreservesCanonicalRightZero [] (zero :: b) | yes r with≡ pr | [] with≡ pr2 rewrite pr | pr2 = applyEquality yes (goZeroEmpty' b pr)
goPreservesCanonicalRightZero [] (zero :: b) | yes r with≡ pr | (x :: xs) with≡ pr2 with inspect (go zero [] (x :: xs))
goPreservesCanonicalRightZero [] (zero :: b) | yes r with≡ pr | (x :: xs) with≡ pr2 | no with≡ pr3 rewrite pr | pr2 | pr3 = exFalso (noNotYes (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero [] i)) (equalityCommutative pr2)) (equalityCommutative (goPreservesCanonicalRightZero [] b)))) (applyEquality (mapMaybe canonical) pr)))
goPreservesCanonicalRightZero [] (zero :: b) | yes r with≡ pr | (x :: xs) with≡ pr2 | yes x₁ with≡ pr3 rewrite pr | pr2 | pr3 = transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (transitivity (transitivity (goPreservesCanonicalRightZero [] b) (applyEquality (λ i → mapMaybe canonical (go zero [] i)) pr2)) (applyEquality (mapMaybe canonical) pr3))
goPreservesCanonicalRightZero [] (one :: b) = refl
goPreservesCanonicalRightZero (zero :: a) [] = refl
goPreservesCanonicalRightZero (one :: a) [] = refl
goPreservesCanonicalRightZero (zero :: a) (zero :: b) with inspect (canonical b)
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | [] with≡ pr1 with inspect (go zero a b)
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | [] with≡ pr1 | no with≡ pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr1) (applyEquality (mapMaybe canonical) (goEmpty a))))))
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | [] with≡ pr1 | yes y with≡ pr2 rewrite pr1 | pr2 = applyEquality yes v
  where
    t : canonical y ≡ canonical a
    t = yesInjective (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr2)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr1) (applyEquality (mapMaybe canonical) (goEmpty a)))))
    v : canonical (zero :: y) ≡ canonical (zero :: a)
    v with inspect (canonical y)
    v | [] with≡ pr4 rewrite pr4 | (transitivity (equalityCommutative t) pr4) = refl
    v | (x :: r) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | (r :: rs) with≡ pr1 with inspect (go zero a b)
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | (r :: rs) with≡ pr1 | no with≡ pr2 with inspect (go zero a (r :: rs))
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | (r :: rs) with≡ pr1 | no with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = refl
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | (r :: rs) with≡ pr1 | no with≡ pr2 | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (transitivity (goPreservesCanonicalRightZero a b) (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr1)) (applyEquality (mapMaybe canonical) pr3))))
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | (r :: rs) with≡ pr1 | yes y with≡ pr2 with inspect (go zero a (r :: rs))
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | (r :: rs) with≡ pr1 | yes y with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) (equalityCommutative pr1)) (equalityCommutative (goPreservesCanonicalRightZero a b))) (applyEquality (mapMaybe canonical) pr2))))
goPreservesCanonicalRightZero (zero :: a) (zero :: b) | (r :: rs) with≡ pr1 | yes y with≡ pr2 | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = applyEquality yes v
  where
    t : canonical y ≡ canonical z
    t = yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr1) (applyEquality (mapMaybe canonical) pr3))))
    v : canonical (zero :: y) ≡ canonical (zero :: z)
    v with inspect (canonical y)
    v | [] with≡ pr4 rewrite pr4 | (transitivity (equalityCommutative t) pr4) = refl
    v | (x :: r) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl
goPreservesCanonicalRightZero (zero :: a) (one :: b) with inspect (go one a b)
goPreservesCanonicalRightZero (zero :: a) (one :: b) | no with≡ x with inspect (go one a (canonical b))
goPreservesCanonicalRightZero (zero :: a) (one :: b) | no with≡ pr | no with≡ pr2 rewrite pr | pr2 = refl
goPreservesCanonicalRightZero (zero :: a) (one :: b) | no with≡ pr | yes x with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (transitivity (goPreservesCanonicalRightOne a b) (applyEquality (mapMaybe canonical) pr2))))
goPreservesCanonicalRightZero (zero :: a) (one :: b) | yes r with≡ pr1 with inspect (go one a (canonical b))
goPreservesCanonicalRightZero (zero :: a) (one :: b) | yes r with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr2)) (transitivity (equalityCommutative (goPreservesCanonicalRightOne a b)) (applyEquality (mapMaybe canonical) pr1))))
goPreservesCanonicalRightZero (zero :: a) (one :: b) | yes r with≡ pr1 | yes s with≡ pr2 rewrite pr1 | pr2 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightOne a b) (applyEquality (mapMaybe canonical) pr2))))
goPreservesCanonicalRightZero (one :: a) (zero :: b) with inspect (go zero a b)
goPreservesCanonicalRightZero (one :: a) (zero :: b) | no with≡ pr1 with inspect (canonical b)
goPreservesCanonicalRightZero (one :: a) (zero :: b) | no with≡ pr1 | [] with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2) (applyEquality (mapMaybe canonical) (goEmpty a))))))
goPreservesCanonicalRightZero (one :: a) (zero :: b) | no with≡ pr1 | (x :: y) with≡ pr2 with inspect (go zero a (x :: y))
goPreservesCanonicalRightZero (one :: a) (zero :: b) | no with≡ pr1 | (x :: y) with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = refl
goPreservesCanonicalRightZero (one :: a) (zero :: b) | no with≡ pr1 | (x :: y) with≡ pr2 | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2) (applyEquality (mapMaybe canonical) pr3)))))
goPreservesCanonicalRightZero (one :: a) (zero :: b) | yes x with≡ pr1 with inspect (canonical b)
goPreservesCanonicalRightZero (one :: a) (zero :: b) | yes x with≡ pr1 | [] with≡ pr2 rewrite pr1 | pr2 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2) (applyEquality (mapMaybe canonical) (goEmpty a))))))
goPreservesCanonicalRightZero (one :: a) (zero :: b) | yes x with≡ pr1 | (r :: rs) with≡ pr2 with inspect (go zero a (r :: rs))
goPreservesCanonicalRightZero (one :: a) (zero :: b) | yes x with≡ pr1 | (r :: rs) with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) (equalityCommutative pr2)) (equalityCommutative (goPreservesCanonicalRightZero a b))) (applyEquality (mapMaybe canonical) pr1))))
goPreservesCanonicalRightZero (one :: a) (zero :: b) | yes x with≡ pr1 | (r :: rs) with≡ pr2 | yes y with≡ pr3 rewrite pr1 | pr2 | pr3 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (transitivity (goPreservesCanonicalRightZero a b) (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2)) (applyEquality (mapMaybe canonical) pr3))))
goPreservesCanonicalRightZero (one :: a) (one :: b) with inspect (go zero a b)
goPreservesCanonicalRightZero (one :: a) (one :: b) | no with≡ pr1 with inspect (go zero a (canonical b))
goPreservesCanonicalRightZero (one :: a) (one :: b) | no with≡ pr1 | no with≡ x rewrite pr1 | x = refl
goPreservesCanonicalRightZero (one :: a) (one :: b) | no with≡ pr1 | yes x₁ with≡ x rewrite pr1 | x = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr1)) (transitivity (goPreservesCanonicalRightZero a b) (applyEquality (mapMaybe canonical) x))))
goPreservesCanonicalRightZero (one :: a) (one :: b) | yes x with≡ pr1 with inspect (go zero a (canonical b))
goPreservesCanonicalRightZero (one :: a) (one :: b) | yes x with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr2)) (transitivity (equalityCommutative (goPreservesCanonicalRightZero a b)) (applyEquality (mapMaybe canonical) pr1))))
goPreservesCanonicalRightZero (one :: a) (one :: b) | yes x with≡ pr1 | yes y with≡ pr2 rewrite pr1 | pr2 = applyEquality yes v
  where
    t : canonical x ≡ canonical y
    t = yesInjective (transitivity (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr1)) (goPreservesCanonicalRightZero a b)) (applyEquality (mapMaybe canonical) pr2))
    v : canonical (zero :: x) ≡ canonical (zero :: y)
    v with inspect (canonical x)
    v | [] with≡ pr4 rewrite pr4 | (transitivity (equalityCommutative t) pr4) = refl
    v | (x :: r) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl

goPreservesCanonicalRightOne a [] = refl
goPreservesCanonicalRightOne [] (zero :: b) rewrite goOneEmpty' (canonical (zero :: b)) = refl
goPreservesCanonicalRightOne (zero :: a) (zero :: b) with inspect (go one a b)
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | no with≡ pr1 with inspect (canonical b)
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | no with≡ pr1 | [] with≡ pr2 with inspect (go one a [])
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | no with≡ pr1 | [] with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = refl
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | no with≡ pr1 | [] with≡ pr2 | yes y with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (transitivity (goPreservesCanonicalRightOne a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go one a i)) pr2) refl)) (applyEquality (mapMaybe canonical) pr3))))
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | no with≡ pr1 | (x :: y) with≡ pr2 with inspect (go one a (x :: y))
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | no with≡ pr1 | (x :: y) with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = refl
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | no with≡ pr1 | (x :: y) with≡ pr2 | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightOne a b) (applyEquality (λ i → mapMaybe canonical (go one a i)) pr2))) (applyEquality (mapMaybe canonical) pr3)))
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | yes y with≡ pr1 with inspect (canonical b)
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | yes y with≡ pr1 | [] with≡ pr2 with inspect (go one a [])
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | yes y with≡ pr1 | [] with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (applyEquality (λ i → mapMaybe canonical (go one a i)) (equalityCommutative pr2)) (equalityCommutative (goPreservesCanonicalRightOne a b)))) (applyEquality (mapMaybe canonical) pr1)))
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | yes y with≡ pr1 | [] with≡ pr2 | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (transitivity (goPreservesCanonicalRightOne a b) (applyEquality (λ i → mapMaybe canonical (go one a i)) pr2)) (applyEquality (mapMaybe canonical) pr3))))
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | yes y with≡ pr1 | (r :: rs) with≡ pr2 with inspect (go one a (r :: rs))
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | yes y with≡ pr1 | (r :: rs) with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (applyEquality (λ i → mapMaybe canonical (go one a i)) (equalityCommutative pr2)) (transitivity (equalityCommutative (goPreservesCanonicalRightOne a b)) (applyEquality (mapMaybe canonical) pr1)))))
goPreservesCanonicalRightOne (zero :: a) (zero :: b) | yes y with≡ pr1 | (r :: rs) with≡ pr2 | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (transitivity (goPreservesCanonicalRightOne a b) (applyEquality (λ i → mapMaybe canonical (go one a i)) pr2)) (applyEquality (mapMaybe canonical) pr3))))
goPreservesCanonicalRightOne (one :: a) (zero :: b) with inspect (go zero a b)
goPreservesCanonicalRightOne (one :: a) (zero :: b) | no with≡ pr1 with inspect (canonical b)
goPreservesCanonicalRightOne (one :: a) (zero :: b) | no with≡ pr1 | [] with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2) (applyEquality (mapMaybe canonical) (goEmpty a))))))
goPreservesCanonicalRightOne (one :: a) (zero :: b) | no with≡ pr1 | (r :: rs) with≡ pr2 with inspect (go zero a (r :: rs))
goPreservesCanonicalRightOne (one :: a) (zero :: b) | no with≡ pr1 | (r :: rs) with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = refl
goPreservesCanonicalRightOne (one :: a) (zero :: b) | no with≡ pr1 | (r :: rs) with≡ pr2 | yes y with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (transitivity (goPreservesCanonicalRightZero a b) (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2)) (applyEquality (mapMaybe canonical) pr3))))
goPreservesCanonicalRightOne (one :: a) (zero :: b) | yes y with≡ pr1 with inspect (canonical b)
goPreservesCanonicalRightOne (one :: a) (zero :: b) | yes y with≡ pr1 | [] with≡ pr2 rewrite pr1 | pr2 = applyEquality yes v
  where
    t : canonical y ≡ canonical a
    t = yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2) (applyEquality (mapMaybe canonical) (goEmpty a)))))
    v : canonical (zero :: y) ≡ canonical (zero :: a)
    v with inspect (canonical y)
    v | [] with≡ pr4 rewrite pr4 | (transitivity (equalityCommutative t) pr4) = refl
    v | (x :: r) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl
goPreservesCanonicalRightOne (one :: a) (zero :: b) | yes y with≡ pr1 | (r :: rs) with≡ pr2 with inspect (go zero a (r :: rs))
goPreservesCanonicalRightOne (one :: a) (zero :: b) | yes y with≡ pr1 | (r :: rs) with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (transitivity (transitivity (goPreservesCanonicalRightZero a b) (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2)) (applyEquality (mapMaybe canonical) pr3))) (applyEquality (mapMaybe canonical) pr1)))
goPreservesCanonicalRightOne (one :: a) (zero :: b) | yes y with≡ pr1 | (r :: rs) with≡ pr2 | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = applyEquality yes v
  where
    t : canonical y ≡ canonical z
    t = yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightZero a b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero a i)) pr2) (applyEquality (mapMaybe canonical) pr3))))
    v : canonical (zero :: y) ≡ canonical (zero :: z)
    v with inspect (canonical y)
    v | [] with≡ pr4 rewrite pr4 | (transitivity (equalityCommutative t) pr4) = refl
    v | (x :: r) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl
goPreservesCanonicalRightOne [] (one :: b) = refl
goPreservesCanonicalRightOne (zero :: a) (one :: b) with inspect (go one a b)
goPreservesCanonicalRightOne (zero :: a) (one :: b) | no with≡ pr1 with inspect (go one a (canonical b))
goPreservesCanonicalRightOne (zero :: a) (one :: b) | no with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = refl
goPreservesCanonicalRightOne (zero :: a) (one :: b) | no with≡ pr1 | yes y with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightOne a b) (applyEquality (mapMaybe canonical) pr2))))
goPreservesCanonicalRightOne (zero :: a) (one :: b) | yes y with≡ pr1 with inspect (go one a (canonical b))
goPreservesCanonicalRightOne (zero :: a) (one :: b) | yes y with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (equalityCommutative (goPreservesCanonicalRightOne a b)) (applyEquality (mapMaybe canonical) pr1))))
goPreservesCanonicalRightOne (zero :: a) (one :: b) | yes y with≡ pr1 | yes z with≡ pr2 rewrite pr1 | pr2 = applyEquality yes v
  where
    t : canonical y ≡ canonical z
    t = yesInjective (transitivity (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr1)) (goPreservesCanonicalRightOne a b)) (applyEquality (mapMaybe canonical) pr2))
    v : canonical (zero :: y) ≡ canonical (zero :: z)
    v with inspect (canonical y)
    v | [] with≡ pr4 rewrite pr4 | (transitivity (equalityCommutative t) pr4) = refl
    v | (x :: r) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl
goPreservesCanonicalRightOne (one :: a) (one :: b) with inspect (go one a b)
goPreservesCanonicalRightOne (one :: a) (one :: b) | no with≡ pr1 with inspect (go one a (canonical b))
goPreservesCanonicalRightOne (one :: a) (one :: b) | no with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = refl
goPreservesCanonicalRightOne (one :: a) (one :: b) | no with≡ pr1 | yes y with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (goPreservesCanonicalRightOne a b) (applyEquality (mapMaybe canonical) pr2))))
goPreservesCanonicalRightOne (one :: a) (one :: b) | yes y with≡ pr1 with inspect (go one a (canonical b))
goPreservesCanonicalRightOne (one :: a) (one :: b) | yes y with≡ pr1 | yes z with≡ pr2 rewrite pr1 | pr2 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr1)) (goPreservesCanonicalRightOne a b) ) (applyEquality (mapMaybe canonical) pr2)))
goPreservesCanonicalRightOne (one :: a) (one :: b) | yes y with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (equalityCommutative (goPreservesCanonicalRightOne a b)) (applyEquality (mapMaybe canonical) pr1))))

goPreservesCanonicalRight : (state : Bit) → (a b : BinNat) → mapMaybe canonical (go state a b) ≡ mapMaybe canonical (go state a (canonical b))
goPreservesCanonicalRight zero = goPreservesCanonicalRightZero
goPreservesCanonicalRight one = goPreservesCanonicalRightOne
