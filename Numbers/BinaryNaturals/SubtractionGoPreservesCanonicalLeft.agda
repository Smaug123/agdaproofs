{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Numbers.Naturals.Naturals
open import Numbers.BinaryNaturals.Definition
open import Maybe
open import Numbers.BinaryNaturals.SubtractionGo

module Numbers.BinaryNaturals.SubtractionGoPreservesCanonicalLeft where

  goPreservesCanonicalLeftZero : (a b : BinNat) → mapMaybe canonical (go zero a b) ≡ mapMaybe canonical (go zero (canonical a) b)
  goPreservesCanonicalLeftOne : (a b : BinNat) → mapMaybe canonical (go one a b) ≡ mapMaybe canonical (go one (canonical a) b)

  goPreservesCanonicalLeftZero [] b = refl
  goPreservesCanonicalLeftZero (zero :: a) [] with inspect (canonical a)
  goPreservesCanonicalLeftZero (zero :: a) [] | [] with≡ pr rewrite pr = refl
  goPreservesCanonicalLeftZero (zero :: a) [] | (x :: t) with≡ pr rewrite pr | transitivity (applyEquality canonical (equalityCommutative pr)) (transitivity (equalityCommutative (canonicalIdempotent a)) pr) = refl
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) with inspect (canonical a)
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | [] with≡ pr with inspect (go zero a b)
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | [] with≡ pr | no with≡ pr2 rewrite pr | pr2 = transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goPreservesCanonicalLeftZero a b) (applyEquality (λ i → mapMaybe canonical (go zero i b)) pr))
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | [] with≡ pr | yes x with≡ pr2 with inspect (canonical x)
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | [] with≡ pr | yes x with≡ pr2 | [] with≡ pr3 rewrite pr | pr2 | pr3 = transitivity (equalityCommutative (transitivity (applyEquality (mapMaybe canonical) pr2) (applyEquality yes pr3))) (transitivity (goPreservesCanonicalLeftZero a b) (applyEquality (λ i → mapMaybe canonical (go zero i b)) pr))
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | [] with≡ pr | yes x with≡ pr2 | (y1 :: ys) with≡ pr3 = exFalso (nonEmptyNotEmpty (goZero b {y1 :: ys} t))
    where
      t : mapMaybe canonical (go zero [] b) ≡ yes (y1 :: ys)
      t = transitivity (transitivity (applyEquality (λ i → mapMaybe canonical (go zero i b)) (equalityCommutative pr)) (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2))) (applyEquality yes pr3)
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | (x :: y) with≡ pr with inspect (go zero a b)
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | (x :: y) with≡ pr | no with≡ pr2 with inspect (go zero (x :: y) b)
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | (x :: y) with≡ pr | no with≡ pr2 | no with≡ pr3 rewrite pr | pr2 | pr3 = refl
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | (x :: y) with≡ pr | no with≡ pr2 | yes r with≡ pr3 = exFalso (noNotYes (transitivity (equalityCommutative (transitivity (applyEquality (λ i → mapMaybe canonical (go zero i b)) (equalityCommutative pr)) (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2)))) (applyEquality (mapMaybe canonical) pr3)))
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | (x :: y) with≡ pr | yes x1 with≡ pr2 with inspect (go zero (x :: y) b)
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | (x :: y) with≡ pr | yes x1 with≡ pr2 | no with≡ pr3 rewrite equalityCommutative pr = exFalso (noNotYes {b = canonical x1} (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr3)) (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2))))
  goPreservesCanonicalLeftZero (zero :: a) (zero :: b) | (x :: y) with≡ pr | yes x1 with≡ pr2 | yes x2 with≡ pr3 with yesInjective {x = canonical x1} {y = canonical x2} (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) (transitivity (applyEquality (λ i → go zero i b) pr) pr3)))
  ... | k rewrite pr | pr2 | pr3 | equalityCommutative pr = applyEquality yes t
    where
      t : canonical (zero :: x1) ≡ canonical (zero :: x2)
      t with inspect (canonical x1)
      t | [] with≡ pr rewrite pr | equalityCommutative k = refl
      t | (x :: bl) with≡ pr rewrite pr | equalityCommutative k = refl
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) with inspect (canonical a)
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | [] with≡ x with inspect (go one a b)
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | [] with≡ pr | no with≡ pr1 rewrite pr | pr1 = refl
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | [] with≡ pr | yes x₂ with≡ pr1 with goPreservesCanonicalLeftOne a b
  ... | bl rewrite pr1 | pr = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) (goOneEmpty' b))) (equalityCommutative bl)))
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | (x₁ :: y) with≡ x with inspect (go one a b)
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | (r :: rs) with≡ pr1 | no with≡ pr2 with inspect (go one (r :: rs) b)
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | (r :: rs) with≡ pr1 | no with≡ pr2 | no with≡ pr3 rewrite pr1 | pr2 | pr3 = refl
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | (r :: rs) with≡ pr1 | no with≡ pr2 | yes x with≡ pr3 rewrite pr1 | pr2 | pr3 | equalityCommutative pr1 = exFalso (noNotYes (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (goPreservesCanonicalLeftOne a b)) (applyEquality (mapMaybe canonical) pr3)))
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | (r :: rs) with≡ pr1 | yes m with≡ pr2 with inspect (go one (r :: rs) b)
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | (r :: rs) with≡ pr1 | yes m with≡ pr2 | no with≡ x rewrite pr1 | pr2 | x | equalityCommutative pr1 = exFalso (noNotYes (transitivity (equalityCommutative (transitivity (goPreservesCanonicalLeftOne a b) (applyEquality (mapMaybe canonical) x))) (applyEquality (mapMaybe canonical) pr2)))
  goPreservesCanonicalLeftZero (zero :: a) (one :: b) | (r :: rs) with≡ pr1 | yes m with≡ pr2 | yes x₁ with≡ x rewrite pr1 | pr2 | x | equalityCommutative pr1 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr2)) (goPreservesCanonicalLeftOne a b)) (applyEquality (mapMaybe canonical) x)))
  goPreservesCanonicalLeftZero (one :: a) [] rewrite equalityCommutative (canonicalIdempotent a) = refl
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) with inspect (canonical a)
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | [] with≡ pr with inspect (go zero a b)
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | [] with≡ pr | no with≡ pr2 with inspect (go zero [] b)
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | [] with≡ pr | no with≡ pr2 | no with≡ pr3 rewrite pr | pr2 | pr3 = refl
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | [] with≡ pr | no with≡ pr2 | yes x with≡ pr3 rewrite pr | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (transitivity (transitivity (applyEquality (λ i → mapMaybe canonical (go zero i b)) (equalityCommutative pr)) (equalityCommutative (goPreservesCanonicalLeftZero a b))) (applyEquality (mapMaybe canonical) pr2))) (applyEquality (mapMaybe canonical) pr3)))
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | [] with≡ pr | yes x with≡ pr2 with inspect (go zero [] b)
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr3)) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero i b)) (equalityCommutative pr)) (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2)))))
  ... | yes y with≡ pr3 rewrite pr | pr2 | pr3 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (transitivity (goPreservesCanonicalLeftZero a b) (applyEquality (λ i → mapMaybe canonical (go zero i b)) pr)) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | (x :: y) with≡ pr with inspect (go zero a b)
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | (x :: y) with≡ pr | no with≡ pr2 with inspect (go zero (x :: y) b)
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 = refl
  ... | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goPreservesCanonicalLeftZero a b) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftZero (one :: a) (zero :: b) | (x :: y) with≡ pr | yes x₁ with≡ pr2 with inspect (go zero (x :: y) b)
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (equalityCommutative (transitivity (goPreservesCanonicalLeftZero a b) (applyEquality (mapMaybe canonical) pr3))) (applyEquality (mapMaybe canonical) pr2)))
  ... | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2))) (applyEquality (mapMaybe canonical) pr3)))
  goPreservesCanonicalLeftZero (one :: a) (one :: b) with inspect (canonical a)
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | [] with≡ x with inspect (go zero a b)
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | [] with≡ pr | no with≡ pr2 with inspect (go zero [] b)
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = refl
  ... | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr2)) (transitivity (goPreservesCanonicalLeftZero a b) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | [] with≡ pr | yes y with≡ pr2 with inspect (go zero [] b)
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr3)) (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2))))
  ... | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = applyEquality yes v
    where
      t : canonical y ≡ canonical z
      t = yesInjective (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr3))
      v : canonical (zero :: y) ≡ canonical (zero :: z)
      v with inspect (canonical y)
      v | [] with≡ pr4 rewrite pr4 | (transitivity (equalityCommutative t) pr4) = refl
      v | (x :: r) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | (r :: rs) with≡ x with inspect (go zero a b)
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | (r :: rs) with≡ pr | no with≡ pr2 with inspect (go zero (r :: rs) b)
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | (r :: rs) with≡ pr | no with≡ pr2 | no with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = refl
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | (r :: rs) with≡ pr | no with≡ pr2 | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goPreservesCanonicalLeftZero a b) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftZero (one :: a) (one :: b) | (r :: rs) with≡ pr | yes y with≡ pr2 with inspect (go zero (r :: rs) b)
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2))))
  ... | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = applyEquality yes v
    where
      t : canonical y ≡ canonical z
      t = yesInjective (transitivity (equalityCommutative (transitivity (equalityCommutative (goPreservesCanonicalLeftZero a b)) (applyEquality (mapMaybe canonical) pr2))) (applyEquality (mapMaybe canonical) pr3))
      v : canonical (zero :: y) ≡ canonical (zero :: z)
      v with inspect (canonical y)
      ... | [] with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl
      ... | (r :: rs) with≡ pr4 rewrite pr4 | transitivity (equalityCommutative t) pr4 = refl

  badLemma : (a b : BinNat) {t : BinNat} → go one a b ≡ yes t → canonical a ≡ [] → False
  badLemma a b pr1 pr2 with applyEquality (mapMaybe canonical) pr1
  badLemma a b pr1 pr2 | t with goPreservesCanonicalLeftOne a b
  ... | th rewrite pr2 | t | goOneEmpty' b = noNotYes (equalityCommutative th)

  goPreservesCanonicalLeftOne [] [] = refl
  goPreservesCanonicalLeftOne [] (x :: b) = refl
  goPreservesCanonicalLeftOne (zero :: a) [] with inspect (canonical a)
  goPreservesCanonicalLeftOne (zero :: a) [] | [] with≡ pr with inspect (go one a [])
  goPreservesCanonicalLeftOne (zero :: a) [] | [] with≡ pr | no with≡ x rewrite pr | x = refl
  goPreservesCanonicalLeftOne (zero :: a) [] | [] with≡ pr | yes y with≡ x rewrite pr | x = exFalso (noNotYes (transitivity (equalityCommutative (transitivity (goPreservesCanonicalLeftOne a []) (transitivity (applyEquality (λ i → mapMaybe canonical (go one i [])) pr) refl))) (applyEquality (mapMaybe canonical) x)))
  goPreservesCanonicalLeftOne (zero :: a) [] | (x :: xs) with≡ pr with inspect (go one a [])
  goPreservesCanonicalLeftOne (zero :: a) [] | (x :: xs) with≡ pr | no with≡ pr2 with inspect (go one (canonical a) [])
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = refl
  ... | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goPreservesCanonicalLeftOne a []) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftOne (zero :: a) [] | (x :: xs) with≡ pr | yes y with≡ pr2 with inspect (go one (x :: xs) [])
  ... | no with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (equalityCommutative (goPreservesCanonicalLeftOne a [])) (applyEquality (mapMaybe canonical) pr2))))
  ... | yes z with≡ pr3 rewrite pr | pr2 | pr3 | equalityCommutative pr = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goPreservesCanonicalLeftOne a []) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftOne (one :: a) [] with inspect (canonical a)
  ... | [] with≡ pr rewrite pr = refl
  ... | (x :: xs) with≡ pr rewrite pr | equalityCommutative pr = applyEquality yes (transitivity (canonicalAscends' {zero} a λ pr2 → nonEmptyNotEmpty (transitivity (equalityCommutative pr) pr2)) (lemma a))
    where
      lemma : (a : BinNat) → canonical (zero :: a) ≡ canonical (zero :: canonical a)
      lemma [] = refl
      lemma (zero :: a) with inspect (canonical a)
      lemma (zero :: a) | [] with≡ pr rewrite pr = refl
      lemma (zero :: a) | (x :: bl) with≡ pr rewrite pr | equalityCommutative pr | equalityCommutative (canonicalIdempotent a) | pr = refl
      lemma (one :: a) rewrite equalityCommutative (canonicalIdempotent a) = refl
  goPreservesCanonicalLeftOne (zero :: as) (zero :: bs) with inspect (go one as bs)
  goPreservesCanonicalLeftOne (zero :: as) (zero :: bs) | no with≡ pr1 with inspect (canonical as)
  goPreservesCanonicalLeftOne (zero :: as) (zero :: bs) | no with≡ pr1 | [] with≡ pr2 rewrite pr1 | pr2 = refl
  goPreservesCanonicalLeftOne (zero :: as) (zero :: bs) | no with≡ pr1 | (a1 :: a) with≡ pr2 with inspect (go one (a1 :: a) bs)
  ... | no with≡ pr3 rewrite pr1 | pr2 | pr3 = refl
  ... | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (transitivity (goPreservesCanonicalLeftOne as bs) (applyEquality (λ i → mapMaybe canonical (go one i bs)) pr2)) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftOne (zero :: as) (zero :: bs) | yes x with≡ pr1 with inspect (canonical as)
  goPreservesCanonicalLeftOne (zero :: as) (zero :: bs) | yes x with≡ pr1 | [] with≡ pr2 rewrite pr1 | pr2 = exFalso (badLemma as bs pr1 pr2)
  goPreservesCanonicalLeftOne (zero :: as) (zero :: bs) | yes x with≡ pr1 | (r :: rs) with≡ pr2 with inspect (go one (r :: rs) bs)
  ... | no with≡ pr3 rewrite pr1 | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (equalityCommutative (transitivity (goPreservesCanonicalLeftOne as bs) (applyEquality (λ i → mapMaybe canonical (go one i bs)) pr2))) (applyEquality (mapMaybe canonical) pr1))))
  ... | yes z with≡ pr3 rewrite pr1 | pr2 | pr3 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr1)) (transitivity (transitivity (goPreservesCanonicalLeftOne as bs) (applyEquality (λ i → mapMaybe canonical (go one i bs)) pr2)) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) with inspect (go one as bs)
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | no with≡ pr with inspect (canonical as)
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | no with≡ pr | [] with≡ pr2 rewrite pr | pr2 = refl
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | no with≡ pr | (r :: rs) with≡ pr2 with inspect (go one (r :: rs) bs)
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | no with≡ pr | (r :: rs) with≡ pr2 | no with≡ pr3 rewrite pr | pr2 | pr3 = refl
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | no with≡ pr | (r :: rs) with≡ pr2 | yes z with≡ pr3 rewrite pr | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (transitivity (transitivity (goPreservesCanonicalLeftOne as bs) (applyEquality (λ i → mapMaybe canonical (go one i bs)) pr2)) (applyEquality (mapMaybe canonical) pr3))))
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | yes x₁ with≡ pr with inspect (canonical as)
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | yes x₁ with≡ pr | [] with≡ pr2 rewrite pr | pr2 = exFalso (badLemma as bs pr pr2)
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | yes x₁ with≡ pr | (r :: rs) with≡ pr2 with inspect (go one (r :: rs) bs)
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | yes x₁ with≡ pr | (r :: rs) with≡ pr2 | no with≡ pr3 rewrite pr | pr2 | pr3 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr3)) (transitivity (transitivity (applyEquality (λ i → mapMaybe canonical (go one i bs)) (equalityCommutative pr2)) (equalityCommutative (goPreservesCanonicalLeftOne as bs))) (applyEquality (mapMaybe canonical) pr))))
  goPreservesCanonicalLeftOne (zero :: as) (one :: bs) | yes x with≡ pr | (r :: rs) with≡ pr2 | yes y with≡ pr3 rewrite pr | pr2 | pr3 = applyEquality yes v
    where
      t : canonical x ≡ canonical y
      t = yesInjective (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (transitivity (transitivity (goPreservesCanonicalLeftOne as bs) (applyEquality (λ i → mapMaybe canonical (go one i bs)) pr2)) (applyEquality (mapMaybe canonical) pr3)))
      v : canonical (zero :: x) ≡ canonical (zero :: y)
      v with inspect (canonical x)
      ... | [] with≡ pr3 rewrite pr3 | transitivity (equalityCommutative t) pr3 = refl
      ... | (r :: rs) with≡ pr3 rewrite pr3 | transitivity (equalityCommutative t) pr3 = refl
  goPreservesCanonicalLeftOne (one :: as) (zero :: bs) with inspect (go zero as bs)
  goPreservesCanonicalLeftOne (one :: as) (zero :: bs) | no with≡ pr with inspect (go zero (canonical as) bs)
  goPreservesCanonicalLeftOne (one :: as) (zero :: bs) | no with≡ pr | no with≡ pr2 rewrite pr | pr2 = refl
  goPreservesCanonicalLeftOne (one :: as) (zero :: bs) | no with≡ pr | yes x with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr)) (transitivity (goPreservesCanonicalLeftZero as bs) (applyEquality (mapMaybe canonical) pr2))))
  goPreservesCanonicalLeftOne (one :: as) (zero :: bs) | yes x with≡ pr with inspect (go zero (canonical as) bs)
  goPreservesCanonicalLeftOne (one :: as) (zero :: bs) | yes x with≡ pr | yes y with≡ pr2 rewrite pr | pr2 = applyEquality yes v
    where
      t : canonical x ≡ canonical y
      t = yesInjective (transitivity (equalityCommutative (transitivity (equalityCommutative (goPreservesCanonicalLeftZero as bs)) (applyEquality (mapMaybe canonical) pr))) (applyEquality (mapMaybe canonical) pr2))
      v : canonical (zero :: x) ≡ canonical (zero :: y)
      v with inspect (canonical x)
      ... | [] with≡ pr3 rewrite pr3 | transitivity (equalityCommutative t) pr3 = refl
      ... | (r :: rs) with≡ pr3 rewrite pr3 | transitivity (equalityCommutative t) pr3 = refl
  goPreservesCanonicalLeftOne (one :: as) (zero :: bs) | yes x with≡ pr | no with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (equalityCommutative (goPreservesCanonicalLeftZero as bs)) (applyEquality (mapMaybe canonical) pr))))
  goPreservesCanonicalLeftOne (one :: as) (one :: bs) with inspect (go one as bs)
  goPreservesCanonicalLeftOne (one :: as) (one :: bs) | y with≡ pr with inspect (go one (canonical as) bs)
  goPreservesCanonicalLeftOne (one :: as) (one :: bs) | no with≡ pr | no with≡ pr2 rewrite pr | pr2 = refl
  goPreservesCanonicalLeftOne (one :: as) (one :: bs) | no with≡ pr | yes x₁ with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (transitivity (goPreservesCanonicalLeftOne as bs) (applyEquality (mapMaybe canonical) pr2))))
  goPreservesCanonicalLeftOne (one :: as) (one :: bs) | yes x₁ with≡ pr | no with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (equalityCommutative (goPreservesCanonicalLeftOne as bs)) (applyEquality (mapMaybe canonical) pr))))
  goPreservesCanonicalLeftOne (one :: as) (one :: bs) | yes x₁ with≡ pr | yes x₂ with≡ pr2 rewrite pr | pr2 = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr)) (goPreservesCanonicalLeftOne as bs)) (applyEquality (mapMaybe canonical) pr2)))

  goPreservesCanonicalLeft : (state : Bit) → (a b : BinNat) → mapMaybe canonical (go state a b) ≡ mapMaybe canonical (go state (canonical a) b)
  goPreservesCanonicalLeft zero = goPreservesCanonicalLeftZero
  goPreservesCanonicalLeft one = goPreservesCanonicalLeftOne
