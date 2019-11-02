{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Semirings.Definition
open import Orders
open import WellFoundedInduction
open import Sets.CantorBijection.Order

module Sets.CantorBijection.Proofs where

  open Sets.CantorBijection.Order using (order ; totalOrder ; orderWellfounded)

  cantorInverseLemma : (ℕ && ℕ) → (ℕ && ℕ)
  cantorInverseLemma (0 ,, s) = (succ s) ,, 0
  cantorInverseLemma (succ r ,, 0) = r ,, 1
  cantorInverseLemma (succ r ,, succ s) = (r ,, succ (succ s))

  cantorInverse : ℕ → (ℕ && ℕ)
  cantorInverse zero = (0 ,, 0)
  cantorInverse (succ z) = cantorInverseLemma (cantorInverse z)

  cantorInverseLemmaInjective : (a b : ℕ && ℕ) → cantorInverseLemma a ≡ cantorInverseLemma b → a ≡ b
  cantorInverseLemmaInjective (zero ,, b) (zero ,, .b) refl = refl
  cantorInverseLemmaInjective (zero ,, b) (succ c ,, zero) ()
  cantorInverseLemmaInjective (zero ,, b) (succ c ,, succ d) ()
  cantorInverseLemmaInjective (succ a ,, zero) (zero ,, d) ()
  cantorInverseLemmaInjective (succ a ,, succ b) (zero ,, d) ()
  cantorInverseLemmaInjective (succ a ,, zero) (succ .a ,, zero) refl = refl
  cantorInverseLemmaInjective (succ a ,, succ b) (succ .a ,, succ .b) refl = refl

  cantorInverseLemmaSurjective : (a : ℕ && ℕ) → (a ≡ (0 ,, 0)) || (Sg (ℕ && ℕ) (λ b → cantorInverseLemma b ≡ a))
  cantorInverseLemmaSurjective (zero ,, zero) = inl refl
  cantorInverseLemmaSurjective (zero ,, succ zero) = inr ((1 ,, 0) , refl)
  cantorInverseLemmaSurjective (zero ,, succ (succ b)) = inr ((1 ,, succ b) , refl)
  cantorInverseLemmaSurjective (succ a ,, zero) = inr ((0 ,, a) , refl)
  cantorInverseLemmaSurjective (succ a ,, succ zero) = inr ((succ (succ a) ,, 0) , refl)
  cantorInverseLemmaSurjective (succ a ,, succ (succ b)) = inr ((succ (succ a) ,, succ b) , refl)

  cantorInverseLemmaNotZero : (a : ℕ && ℕ) → (cantorInverseLemma a ≡ (0 ,, 0)) → False
  cantorInverseLemmaNotZero (succ a ,, zero) ()
  cantorInverseLemmaNotZero (succ a ,, succ b) ()

  cantorInverseLemmaIncreases : (x : ℕ && ℕ) → order x (cantorInverseLemma x)
  cantorInverseLemmaIncreases (zero ,, b) = inl (identityOfIndiscernablesRight _<N_ (a<SuccA b) (applyEquality succ (equalityCommutative (Semiring.sumZeroRight ℕSemiring b))))
  cantorInverseLemmaIncreases (succ a ,, zero) = inr (transitivity (applyEquality succ (Semiring.sumZeroRight ℕSemiring a)) (Semiring.commutative ℕSemiring 1 a) ,, (le 0 refl))
  cantorInverseLemmaIncreases (succ a ,, succ b) = inr (transitivity (applyEquality succ (Semiring.commutative ℕSemiring a (succ b))) (Semiring.commutative ℕSemiring (succ (succ b)) a) ,, (le 0 refl))

  cantorInverseOrderPreserving : (x y : ℕ) → (x <N y) → order (cantorInverse x) (cantorInverse y)
  cantorInverseOrderPreserving zero (succ y) x<y with TotalOrder.totality totalOrder (0 ,, 0) (cantorInverseLemma (cantorInverse y))
  cantorInverseOrderPreserving zero (succ y) x<y | inl (inl bl) = bl
  cantorInverseOrderPreserving zero (succ y) x<y | inl (inr bl) = exFalso (leastElement bl)
  cantorInverseOrderPreserving zero (succ y) x<y | inr x = exFalso (leastElement {cantorInverse y} (identityOfIndiscernablesRight order (cantorInverseLemmaIncreases (cantorInverse y)) (equalityCommutative x)))
  cantorInverseOrderPreserving (succ x) (succ y) x<y with cantorInverseOrderPreserving x y (canRemoveSuccFrom<N x<y)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr with cantorInverse x
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | x1 ,, x2 with cantorInverse y
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, zero | zero ,, succ y2 = inl (succPreservesInequality (succIsPositive (y2 +N 0)))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, zero | succ y1 ,, zero with TotalOrder.totality ℕTotalOrder 1 (y1 +N 1)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, zero | succ y1 ,, zero | inl (inl pr1) = inl pr1
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, zero | succ y1 ,, zero | inl (inr pr1) rewrite Semiring.commutative ℕSemiring y1 1 = exFalso (zeroNeverGreater (canRemoveSuccFrom<N pr1))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, zero | succ y1 ,, zero | inr pr1 = inr (pr1 ,, le 0 refl)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, zero | succ y1 ,, succ y2 rewrite Semiring.commutative ℕSemiring y1 (succ (succ y2)) = inl (succPreservesInequality (succIsPositive (y2 +N y1)))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | succ x1 ,, zero | zero ,, succ y2 rewrite Semiring.commutative ℕSemiring x1 1 | Semiring.sumZeroRight ℕSemiring y2 | Semiring.sumZeroRight ℕSemiring x1 = inl (TotalOrder.<Transitive ℕTotalOrder pr (a<SuccA _))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | succ x1 ,, zero | succ y1 ,, zero rewrite Semiring.commutative ℕSemiring x1 1 | Semiring.commutative ℕSemiring y1 1 | Semiring.sumZeroRight ℕSemiring x1 | Semiring.sumZeroRight ℕSemiring y1 = inl pr
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | succ x1 ,, zero | succ y1 ,, succ y2 rewrite Semiring.commutative ℕSemiring x1 1 | Semiring.sumZeroRight ℕSemiring x1 = inl (identityOfIndiscernablesRight _<N_ pr (transitivity (applyEquality succ (Semiring.commutative ℕSemiring y1 (succ y2))) (Semiring.commutative ℕSemiring (succ (succ y2)) y1)))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, succ x2 | zero ,, succ y2 rewrite Semiring.sumZeroRight ℕSemiring x2 | Semiring.sumZeroRight ℕSemiring y2 = inl (succPreservesInequality pr)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, succ x2 | succ y1 ,, zero rewrite Semiring.commutative ℕSemiring y1 1 | Semiring.sumZeroRight ℕSemiring y1 | Semiring.sumZeroRight ℕSemiring x2 = ans
    where
      ans : (succ (succ x2) <N succ y1) || (succ (succ x2) ≡ succ y1) && (zero <N 1)
      ans with TotalOrder.totality ℕTotalOrder (succ (succ x2)) (succ y1)
      ans | inl (inl x) = inl x
      ans | inl (inr x) = exFalso (noIntegersBetweenXAndSuccX (succ x2) pr x)
      ans | inr x = inr (x ,, le zero refl)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | zero ,, succ x2 | succ y1 ,, succ y2 rewrite Semiring.commutative ℕSemiring y1 1 | Semiring.sumZeroRight ℕSemiring y1 | Semiring.sumZeroRight ℕSemiring x2 = ans
    where
      ans : (succ (succ x2) <N y1 +N succ (succ y2)) || (succ (succ x2) ≡ y1 +N succ (succ y2)) && (zero <N succ (succ y2))
      ans with TotalOrder.totality ℕTotalOrder (succ (succ x2)) (y1 +N succ (succ y2))
      ans | inl (inl x) = inl x
      ans | inl (inr x) = exFalso (noIntegersBetweenXAndSuccX (succ x2) pr (identityOfIndiscernablesLeft _<N_ x (transitivity (Semiring.commutative ℕSemiring y1 (succ (succ y2))) (applyEquality succ (Semiring.commutative ℕSemiring (succ y2) y1)))))
      ans | inr x = inr (x ,, succIsPositive (succ y2))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | succ x1 ,, succ x2 | zero ,, succ y2 rewrite Semiring.sumZeroRight ℕSemiring y2 = inl (TotalOrder.<Transitive ℕTotalOrder (identityOfIndiscernablesLeft _<N_ pr (transitivity (applyEquality succ (Semiring.commutative ℕSemiring x1 (succ x2))) (Semiring.commutative ℕSemiring (succ (succ x2)) x1))) (a<SuccA (succ y2)))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | succ x1 ,, succ x2 | succ y1 ,, zero rewrite Semiring.commutative ℕSemiring y1 1 | Semiring.sumZeroRight ℕSemiring y1 | Semiring.commutative ℕSemiring x1 (succ x2) | Semiring.commutative ℕSemiring x1 (succ (succ x2)) = inl pr
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inl pr | succ x1 ,, succ x2 | succ y1 ,, succ y2 rewrite Semiring.commutative ℕSemiring x1 (succ x2) | Semiring.commutative ℕSemiring y1 (succ y2) | Semiring.commutative ℕSemiring x1 (succ (succ x2)) | Semiring.commutative ℕSemiring y1 (succ (succ y2)) = inl pr
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (fst ,, snd) with cantorInverse x
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (fst ,, snd) | x1 ,, x2 with cantorInverse y
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (fst ,, ()) | zero ,, zero | zero ,, zero
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (() ,, snd) | zero ,, zero | zero ,, succ y2
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (refl ,, snd) | zero ,, succ .y2 | zero ,, succ y2 = exFalso (TotalOrder.irreflexive ℕTotalOrder snd)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (refl ,, snd) | zero ,, succ .(y1 +N succ y2) | succ y1 ,, succ y2 = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder snd (identityOfIndiscernablesRight _<N_ (addingIncreases (succ y2) y1) (Semiring.commutative ℕSemiring (succ y2) (succ y1)))))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (fst ,, snd) | succ x1 ,, zero | zero ,, succ y2 rewrite Semiring.sumZeroRight ℕSemiring x1 | succInjective fst | Semiring.commutative ℕSemiring y2 1 | Semiring.sumZeroRight ℕSemiring y2 = inl (le zero refl)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (fst ,, snd) | succ x1 ,, zero | succ y1 ,, succ y2 rewrite Semiring.commutative ℕSemiring x1 1 | Semiring.sumZeroRight ℕSemiring x1 = inr (transitivity fst (transitivity (applyEquality succ (Semiring.commutative ℕSemiring y1 (succ y2))) (Semiring.commutative ℕSemiring (succ (succ y2)) y1)) ,, succPreservesInequality snd)
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (fst ,, snd) | succ x1 ,, succ x2 | zero ,, succ y2 rewrite Semiring.sumZeroRight ℕSemiring y2 | Semiring.commutative ℕSemiring x1 (succ x2) | Semiring.commutative ℕSemiring (succ (succ x2)) x1 | fst = inl (succPreservesInequality (le zero refl))
  cantorInverseOrderPreserving (succ x) (succ y) x<y | inr (fst ,, snd) | succ x1 ,, succ x2 | succ y1 ,, succ y2 = inr (transitivity (transitivity (Semiring.commutative ℕSemiring x1 (succ (succ x2))) (applyEquality succ (Semiring.commutative ℕSemiring (succ x2) x1))) (transitivity fst (transitivity (applyEquality succ (Semiring.commutative ℕSemiring y1 (succ y2))) (Semiring.commutative ℕSemiring (succ (succ y2)) y1))) ,, succPreservesInequality snd)

  cantorInverseInjective : (a b : ℕ) → cantorInverse a ≡ cantorInverse b → a ≡ b
  cantorInverseInjective zero zero pr = refl
  cantorInverseInjective zero (succ b) pr = exFalso (cantorInverseLemmaNotZero _ (equalityCommutative pr))
  cantorInverseInjective (succ a) zero pr = exFalso (cantorInverseLemmaNotZero _ pr)
  cantorInverseInjective (succ a) (succ b) pr = applyEquality succ (cantorInverseInjective a b (cantorInverseLemmaInjective (cantorInverse a) (cantorInverse b) pr))

-- Some unnecessary things on the way to the final proof
  cantorInverseDiscrete : (a : ℕ) → (c : ℕ && ℕ) → order (cantorInverse a) c → order c (cantorInverse (succ a)) → False
  cantorInverseDiscrete zero (zero ,, zero) (inl ()) c<sa
  cantorInverseDiscrete zero (zero ,, zero) (inr ()) c<sa
  cantorInverseDiscrete zero (zero ,, succ c) a<c (inl x) = zeroNeverGreater (canRemoveSuccFrom<N x)
  cantorInverseDiscrete zero (succ b ,, zero) a<c (inl x) = zeroNeverGreater (canRemoveSuccFrom<N x)
  cantorInverseDiscrete zero (succ b ,, succ c) a<c (inl x) = zeroNeverGreater (canRemoveSuccFrom<N x)
  cantorInverseDiscrete (succ a) (b ,, c) a<c c<sa with cantorInverse a
  cantorInverseDiscrete (succ a) (zero ,, zero) (inl ()) (inl x) | zero ,, zero
  cantorInverseDiscrete (succ a) (zero ,, zero) (inr ()) (inl x) | zero ,, zero
  cantorInverseDiscrete (succ a) (zero ,, succ zero) a<c (inl x) | zero ,, zero = TotalOrder.irreflexive ℕTotalOrder x
  cantorInverseDiscrete (succ a) (zero ,, succ (succ c)) a<c (inl x) | zero ,, zero = zeroNeverGreater (canRemoveSuccFrom<N x)
  cantorInverseDiscrete (succ a) (succ b ,, c) a<c (inl x) | zero ,, zero = zeroNeverGreater (canRemoveSuccFrom<N x)
  cantorInverseDiscrete (succ a) (b ,, zero) (inl x) (inr (fst ,, snd)) | zero ,, zero = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesRight _<N_ x fst)
  cantorInverseDiscrete (succ a) (b ,, succ c) a<c (inr (fst ,, snd)) | zero ,, zero = zeroNeverGreater (canRemoveSuccFrom<N snd)
  cantorInverseDiscrete (succ a) (b ,, c) (inl y) (inl x) | zero ,, succ snd rewrite Semiring.commutative ℕSemiring snd 1 | Semiring.sumZeroRight ℕSemiring snd = TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder x y)
  cantorInverseDiscrete (succ a) (b ,, succ c) (inr (fst ,, _)) (inl x) | zero ,, succ snd rewrite Semiring.commutative ℕSemiring snd 1 | Semiring.sumZeroRight ℕSemiring snd | fst = TotalOrder.irreflexive ℕTotalOrder x
  cantorInverseDiscrete (succ a) (b ,, zero) (inl x) (inr (fst ,, snd₁)) | zero ,, succ snd rewrite fst | Semiring.commutative ℕSemiring snd 1 | Semiring.sumZeroRight ℕSemiring snd = TotalOrder.irreflexive ℕTotalOrder x
  cantorInverseDiscrete (succ a) (b ,, succ c) (inl x) (inr (fst ,, snd1)) | zero ,, succ snd = zeroNeverGreater (canRemoveSuccFrom<N snd1)
  cantorInverseDiscrete (succ a) (b ,, succ zero) (inr (fst ,, _)) (inr (fst₁ ,, bad)) | zero ,, succ snd = TotalOrder.irreflexive ℕTotalOrder bad
  cantorInverseDiscrete (succ a) (b ,, succ (succ c)) (inr (fst ,, _)) (inr (fst₁ ,, bad)) | zero ,, succ snd = zeroNeverGreater (canRemoveSuccFrom<N bad)
  cantorInverseDiscrete (succ a) (b ,, c) (inl x1) (inl x) | succ zero ,, zero = noIntegersBetweenXAndSuccX 1 x1 x
  cantorInverseDiscrete (succ a) (zero ,, succ zero) (inr (fst ,, snd)) (inl x) | succ zero ,, zero = TotalOrder.irreflexive ℕTotalOrder snd
  cantorInverseDiscrete (succ a) (succ b ,, succ c) (inr (fst ,, snd)) (inl x) | succ zero ,, zero rewrite Semiring.commutative ℕSemiring b (succ c) = bad fst
    where
      bad : {a : ℕ} → 1 ≡ succ (succ a) → False
      bad ()
  cantorInverseDiscrete (succ a) (b ,, c) (inl y) (inl x) | succ (succ fst) ,, zero rewrite Semiring.commutative ℕSemiring fst 2 | Semiring.commutative ℕSemiring fst 1 = TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder y x)
  cantorInverseDiscrete (succ a) (b ,, c) (inr (bad ,, _)) (inl x) | succ (succ fst) ,, zero rewrite Semiring.commutative ℕSemiring fst 2 | Semiring.commutative ℕSemiring fst 1 = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesRight _<N_ x bad)
  cantorInverseDiscrete (succ a) (b ,, c) (inl x) (inr (bad ,, snd)) | succ (succ fst) ,, zero rewrite Semiring.commutative ℕSemiring fst 2 | Semiring.commutative ℕSemiring fst 1 = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesRight _<N_ x bad)
  cantorInverseDiscrete (succ a) (b ,, c) (inr (_ ,, bad)) (inr (fst₁ ,, snd)) | succ (succ fst) ,, zero rewrite Semiring.commutative ℕSemiring fst 2 | Semiring.commutative ℕSemiring fst 1 = noIntegersBetweenXAndSuccX 1 bad snd
  cantorInverseDiscrete (succ a) (b ,, c) (inl x) (inl y) | succ zero ,, succ snd rewrite Semiring.sumZeroRight ℕSemiring snd = noIntegersBetweenXAndSuccX (succ (succ snd)) x y
  cantorInverseDiscrete (succ a) (zero ,, c) (inr (fst ,, snd1)) (inl y) | succ zero ,, succ snd rewrite Semiring.sumZeroRight ℕSemiring snd = noIntegersBetweenXAndSuccX (succ (succ snd)) snd1 y
  cantorInverseDiscrete (succ a) (succ b ,, c) (inr (fst ,, bad)) (inl y) | succ zero ,, succ snd rewrite Semiring.sumZeroRight ℕSemiring snd | fst = TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder bad (identityOfIndiscernablesRight _<N_ (addingIncreases c b) (Semiring.commutative ℕSemiring c (succ b))))
  cantorInverseDiscrete (succ a) (b ,, c) (inl x) (inl y) | succ (succ fst) ,, succ snd rewrite Semiring.commutative ℕSemiring fst (succ (succ (succ snd))) | Semiring.commutative ℕSemiring (succ (succ snd)) fst = TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder y x)
  cantorInverseDiscrete (succ a) (b ,, c) (inl x) (inr (y ,, z)) | succ (succ fst) ,, succ snd rewrite y | Semiring.commutative ℕSemiring fst (succ (succ (succ snd))) | Semiring.commutative ℕSemiring (succ (succ snd)) fst = TotalOrder.irreflexive ℕTotalOrder x
  cantorInverseDiscrete (succ a) (b ,, c) (inr (x ,, y)) (inl z) | succ (succ fst) ,, succ snd rewrite equalityCommutative x | Semiring.commutative ℕSemiring fst (succ (succ (succ snd))) | Semiring.commutative ℕSemiring (succ (succ snd)) fst = TotalOrder.irreflexive ℕTotalOrder z
  cantorInverseDiscrete (succ a) (b ,, c) (inr (x ,, y)) (inr (m ,, n)) | succ (succ fst) ,, succ snd = noIntegersBetweenXAndSuccX (succ (succ snd)) y n

  boundedInversesExist : (a : ℕ && ℕ) (s : ℕ) → order a (cantorInverse s) → Sg ℕ (λ i → cantorInverse i ≡ a)
  boundedInversesExist a zero a<s = exFalso (leastElement a<s)
  boundedInversesExist a (succ s) a<s with TotalOrder.totality totalOrder a (cantorInverse s)
  boundedInversesExist a (succ s) _ | inl (inl a<s) = boundedInversesExist a s a<s
  boundedInversesExist a (succ s) a<s | inl (inr s<a) = exFalso (cantorInverseDiscrete s a s<a a<s)
  boundedInversesExist a (succ s) a<s | inr a=s = s , equalityCommutative a=s

  cantorInverseSurjective : (x : ℕ && ℕ) → Sg ℕ (λ i → (cantorInverse i) ≡ x)
  cantorInverseSurjective = rec orderWellfounded (λ z → Sg ℕ (λ z₁ → (cantorInverse z₁) ≡ z)) go
    where
      go : (a : ℕ && ℕ) → (pr : (x : ℕ && ℕ) (x₁ : order x a) → Sg ℕ (λ z → (cantorInverse z) ≡ x)) → Sg ℕ (λ i → (cantorInverse i) ≡ a)
      go a pr with cantorInverseLemmaSurjective a
      go .(0 ,, 0) pr | inl refl = 0 , refl
      go a ind | inr (decr , proof) with ind decr (identityOfIndiscernablesRight order (cantorInverseLemmaIncreases decr) proof)
      go a ind | inr (decr , proof) | boundForDecr , boundIsBound = succ boundForDecr , transitivity (applyEquality cantorInverseLemma boundIsBound) proof
