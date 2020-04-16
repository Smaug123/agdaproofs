{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Addition

module Numbers.Naturals.Multiplication where

infix 25 _*N_
_*N_ : ℕ → ℕ → ℕ
zero *N y = zero
(succ x) *N y = y +N (x *N y)
{-# BUILTIN NATTIMES _*N_ #-}

productZeroIsZeroLeft : (a : ℕ) → (zero *N a ≡ zero)
productZeroIsZeroLeft a = refl

productZeroIsZeroRight : (a : ℕ) → (a *N zero ≡ zero)
productZeroIsZeroRight zero = refl
productZeroIsZeroRight (succ a) = productZeroIsZeroRight a

productWithOneLeft : (a : ℕ) → ((succ zero) *N a) ≡ a
productWithOneLeft a = transitivity refl (transitivity (applyEquality (λ { m -> a +N m }) refl) (additionNIsCommutative a zero))

productWithOneRight : (a : ℕ) → a *N succ zero ≡ a
productWithOneRight zero = refl
productWithOneRight (succ a) = transitivity refl (addingPreservesEqualityLeft (succ zero) (productWithOneRight a))

productDistributes : (a b c : ℕ) → (a *N (b +N c)) ≡ a *N b +N a *N c
productDistributes zero b c = refl
productDistributes (succ a) b c = transitivity refl
  (transitivity (addingPreservesEqualityLeft (b +N c) (productDistributes a b c))
    (transitivity (equalityCommutative (additionNIsAssociative (b +N c) (a *N b) (a *N c)))
      (transitivity (addingPreservesEqualityRight (a *N c) (additionNIsCommutative (b +N c) (a *N b)))
        (transitivity (addingPreservesEqualityRight (a *N c) (equalityCommutative (additionNIsAssociative (a *N b) b c)))
          (transitivity (addingPreservesEqualityRight (a *N c) (addingPreservesEqualityRight c (additionNIsCommutative (a *N b) b)))
            (transitivity (addingPreservesEqualityRight (a *N c) (addingPreservesEqualityRight {b +N a *N b} {(succ a) *N b} c (refl)))
              (transitivity (additionNIsAssociative ((succ a) *N b) c (a *N c))
                (transitivity (addingPreservesEqualityLeft (succ a *N b) refl)
                  refl)
            )
        ))))))

productPreservesEqualityLeft : (a : ℕ) → {b c : ℕ} → b ≡ c → a *N b ≡ a *N c
productPreservesEqualityLeft a {b} {.b} refl = refl

aSucB : (a b : ℕ) → a *N succ b ≡ a *N b +N a
aSucB a b = transitivity {_} {ℕ} {a *N succ b} {a *N (b +N succ zero)} (productPreservesEqualityLeft a (succIsAddOne b)) (transitivity {_} {ℕ} {a *N (b +N succ zero)} {a *N b +N a *N succ zero} (productDistributes a b (succ zero)) (addingPreservesEqualityLeft (a *N b) (productWithOneRight a)))

aSucBRight : (a b : ℕ) → (succ a) *N b ≡ a *N b +N b
aSucBRight a b = additionNIsCommutative b (a *N b)

multiplicationNIsCommutative : (a b : ℕ) → (a *N b) ≡ (b *N a)
multiplicationNIsCommutative zero b = transitivity (productZeroIsZeroLeft b) (equalityCommutative (productZeroIsZeroRight b))
multiplicationNIsCommutative (succ a) zero = multiplicationNIsCommutative a zero
multiplicationNIsCommutative (succ a) (succ b) = transitivity refl
  (transitivity (addingPreservesEqualityLeft (succ b) (aSucB a b))
    (transitivity (additionNIsCommutative (succ b) (a *N b +N a))
      (transitivity (additionNIsAssociative (a *N b) a (succ b))
        (transitivity (addingPreservesEqualityLeft (a *N b) (succCanMove a b))
          (transitivity (addingPreservesEqualityLeft (a *N b) (additionNIsCommutative (succ a) b))
            (transitivity (equalityCommutative (additionNIsAssociative (a *N b) b (succ a)))
              (transitivity (addingPreservesEqualityRight (succ a) (equalityCommutative (aSucBRight a b)))
                (transitivity (addingPreservesEqualityRight (succ a) (multiplicationNIsCommutative (succ a) b))
                  (transitivity (additionNIsCommutative (b *N (succ a)) (succ a))
                    refl
                )))))))))

productDistributes' : (a b c : ℕ) → (a +N b) *N c ≡ a *N c +N b *N c
productDistributes' a b c rewrite multiplicationNIsCommutative (a +N b) c | productDistributes c a b | multiplicationNIsCommutative c a | multiplicationNIsCommutative c b = refl

flipProductsWithinSum : (a b c : ℕ) → (c *N a +N c *N b ≡ a *N c +N b *N c)
flipProductsWithinSum a b c = transitivity (addingPreservesEqualityRight (c *N b) (multiplicationNIsCommutative c a)) ((addingPreservesEqualityLeft (a *N c) (multiplicationNIsCommutative c b)))

productDistributesRight : (a b c : ℕ) → (a +N b) *N c ≡ a *N c +N b *N c
productDistributesRight a b c = transitivity (multiplicationNIsCommutative (a +N b) c) (transitivity (productDistributes c a b) (flipProductsWithinSum a b c))

multiplicationNIsAssociative : (a b c : ℕ) → (a *N (b *N c)) ≡ ((a *N b) *N c)
multiplicationNIsAssociative zero b c = refl
multiplicationNIsAssociative (succ a) b c =
    transitivity refl
      (transitivity refl
        (transitivity (applyEquality ((λ x → b *N c +N x)) (multiplicationNIsAssociative a b c)) (transitivity (equalityCommutative (productDistributesRight b (a *N b) c)) refl)))

productOne : {a b : ℕ} → a ≡ a *N b → (a ≡ 0) || (b ≡ 1)
productOne {zero} {b} pr = inl refl
productOne {succ a} {zero} pr rewrite multiplicationNIsCommutative a 0 = exFalso (naughtE (equalityCommutative pr))
productOne {succ a} {succ zero} pr = inr refl
productOne {succ a} {succ (succ b)} pr rewrite multiplicationNIsCommutative a (succ (succ b)) | additionNIsCommutative (succ b) (a +N (a +N b *N a)) | additionNIsAssociative (succ a) (a +N b *N a) (succ b) | additionNIsCommutative (a +N b *N a) (succ b) = exFalso (bad pr)
  where
    bad' : {x : ℕ} → x ≡ succ x → False
    bad' ()
    bad : {x y : ℕ} → x ≡ x +N succ y → False
    bad {succ x} {zero} pr rewrite additionNIsCommutative x 1 = bad' pr
    bad {succ x} {succ y} pr = bad (succInjective pr)
