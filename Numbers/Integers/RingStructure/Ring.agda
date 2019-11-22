{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Multiplication
open import Semirings.Definition
open import Groups.Definition
open import Rings.Definition
open import Setoids.Setoids

module Numbers.Integers.RingStructure.Ring where

open import Numbers.Integers.Definition public
open import Numbers.Integers.Addition public
open import Numbers.Integers.Multiplication public

*ZCommutative : (a b : ℤ) → a *Z b ≡ b *Z a
*ZCommutative (nonneg x) (nonneg y) = applyEquality nonneg (multiplicationNIsCommutative x y)
*ZCommutative (nonneg zero) (negSucc y) = refl
*ZCommutative (nonneg (succ x)) (negSucc y) = refl
*ZCommutative (negSucc x) (nonneg zero) = refl
*ZCommutative (negSucc x) (nonneg (succ y)) = refl
*ZCommutative (negSucc x) (negSucc y) = applyEquality nonneg (multiplicationNIsCommutative (succ x) (succ y))

*ZleftIdent : (a : ℤ) → (nonneg 1) *Z a ≡ a
*ZleftIdent (nonneg x) = applyEquality nonneg (Semiring.commutative ℕSemiring x 0)
*ZleftIdent (negSucc x) = applyEquality negSucc (transitivity (Semiring.commutative ℕSemiring (x +N 0) 0) (Semiring.commutative ℕSemiring x 0))

*ZrightIdent : (a : ℤ) → a *Z (nonneg 1) ≡ a
*ZrightIdent (nonneg x) = applyEquality nonneg (Semiring.productOneRight ℕSemiring x)
*ZrightIdent (negSucc x) = applyEquality negSucc (transitivity (Semiring.commutative ℕSemiring (x +N 0) 0) (Semiring.commutative ℕSemiring x 0))

*ZZeroLeft : (a : ℤ) → nonneg 0 *Z a ≡ nonneg 0
*ZZeroLeft (nonneg x) = refl
*ZZeroLeft (negSucc x) = refl

*ZZeroRight : (a : ℤ) → a *Z nonneg 0 ≡ nonneg 0
*ZZeroRight (nonneg x) = applyEquality nonneg (Semiring.productZeroRight ℕSemiring x)
*ZZeroRight (negSucc x) = refl

*ZAssociative : (a b c : ℤ) → a *Z (b *Z c) ≡ (a *Z b) *Z c
*ZAssociative (nonneg zero) b c = transitivity (*ZZeroLeft (b *Z c)) (transitivity (equalityCommutative (*ZZeroLeft c)) (applyEquality (_*Z c) (equalityCommutative (*ZZeroLeft b))))
*ZAssociative (nonneg (succ a)) (nonneg zero) c rewrite Semiring.productZeroRight ℕSemiring a | *ZZeroLeft c | Semiring.productZeroRight ℕSemiring a = refl
*ZAssociative (nonneg (succ a)) (nonneg (succ b)) (nonneg zero) rewrite Semiring.productZeroRight ℕSemiring b | Semiring.productZeroRight ℕSemiring (b +N a *N succ b) | Semiring.productZeroRight ℕSemiring a = refl
*ZAssociative (nonneg (succ a)) (nonneg (succ b)) (nonneg (succ c)) = applyEquality nonneg (Semiring.*Associative ℕSemiring (succ a) (succ b) (succ c))
*ZAssociative (nonneg (succ a)) (nonneg (succ b)) (negSucc x) rewrite productDistributes' b (a *N succ b) x | Semiring.+Associative ℕSemiring x (b *N x) ((a *N succ b) *N x) | equalityCommutative (Semiring.+Associative ℕSemiring ((x +N b *N x) +N b) (a *N ((x +N b *N x) +N b)) a) | equalityCommutative (Semiring.+Associative ℕSemiring (x +N b *N x) ((a *N succ b) *N x) (b +N a *N succ b)) | equalityCommutative (Semiring.+Associative ℕSemiring (x +N b *N x) b (a *N ((x +N b *N x) +N b) +N a)) = applyEquality (λ i → negSucc ((x +N b *N x) +N i)) ans
  where
    ans3 : (succ b +N (succ b *N x)) *N a ≡ succ x *N (a *N succ b)
    ans3 rewrite multiplicationNIsCommutative (succ b) x = transitivity (equalityCommutative (Semiring.*Associative ℕSemiring (succ x) (succ b) a)) (applyEquality (succ x *N_) (multiplicationNIsCommutative (succ b) a))
    ans2 : a *N ((x +N b *N x) +N b) +N a ≡ (a *N succ b) +N (a *N succ b) *N x
    ans2 rewrite multiplicationNIsCommutative (a *N succ b) x | Semiring.commutative ℕSemiring (succ b *N x) b | multiplicationNIsCommutative a (b +N (succ b *N x)) | Semiring.commutative ℕSemiring ((b +N (succ b *N x)) *N a) a = ans3
    ans : b +N (a *N ((x +N b *N x) +N b) +N a) ≡ (a *N succ b) *N x +N (b +N a *N succ b)
    ans rewrite Semiring.commutative ℕSemiring ((a *N succ b) *N x) (b +N a *N succ b) | equalityCommutative (Semiring.+Associative ℕSemiring b (a *N succ b) ((a *N succ b) *N x)) = applyEquality (b +N_) ans2
*ZAssociative (nonneg (succ a)) (negSucc b) (nonneg zero) = applyEquality nonneg (Semiring.productZeroRight ℕSemiring a)
*ZAssociative (nonneg (succ a)) (negSucc b) (nonneg (succ c)) = applyEquality negSucc ans
  where
    ans4 : (b +N b *N c) +N (a *N b +N (a *N b) *N c) ≡ (b +N a *N b) +N (b *N c +N (a *N b) *N c)
    ans4 rewrite Semiring.+Associative ℕSemiring (b +N b *N c) (a *N b) ((a *N b) *N c) | Semiring.+Associative ℕSemiring (b +N a *N b) (b *N c) ((a *N b) *N c) = applyEquality (_+N (a *N b) *N c) (transitivity (transitivity (applyEquality (_+N a *N b) (Semiring.commutative ℕSemiring b (b *N c))) (equalityCommutative (Semiring.+Associative ℕSemiring (b *N c) b (a *N b)))) (Semiring.commutative ℕSemiring (b *N c) (b +N a *N b)))
    ans3 : ((b +N b *N c) +N (a *N b +N (a *N b) *N c)) +N ((c +N a *N c) +N a) ≡ ((b +N a *N b) +N (b *N c +N (a *N b) *N c)) +N ((a +N a *N c) +N c)
    ans3 rewrite Semiring.commutative ℕSemiring (c +N a *N c) a | Semiring.commutative ℕSemiring c (a *N c) | Semiring.+Associative ℕSemiring a (a *N c) c = applyEquality (λ i → i +N ((a +N a *N c) +N c)) {(b +N b *N c) +N (a *N b +N (a *N b) *N c)} {(b +N a *N b) +N (b *N c +N (a *N b) *N c)} ans4
    ans2 : (((b +N c *N b) +N (a *N b +N a *N (c *N b))) +N (c +N a *N c)) +N a ≡ (((b +N a *N b) +N (c *N b +N c *N (a *N b))) +N (a +N c *N a)) +N c
    ans2 rewrite multiplicationNIsCommutative c b | multiplicationNIsCommutative c (a *N b) | Semiring.*Associative ℕSemiring a b c | multiplicationNIsCommutative c a = transitivity (equalityCommutative (Semiring.+Associative ℕSemiring ((b +N b *N c) +N (a *N b +N (a *N b) *N c)) (c +N a *N c) a)) (transitivity ans3 (Semiring.+Associative ℕSemiring ((b +N a *N b) +N (b *N c +N (a *N b) *N c)) (a +N a *N c) c))
    ans : succ a *N ((succ c *N b) +N c) +N a ≡ succ c *N ((succ a *N b) +N a) +N c
    ans = transitivity (applyEquality (_+N a) (productDistributes (succ a) (succ c *N b) c)) (transitivity (transitivity (applyEquality (λ i → ((((b +N c *N b) +N i) +N (c +N a *N c)) +N a)) (productDistributes a b (c *N b))) (transitivity ans2 (applyEquality (λ i → (((b +N a *N b) +N i) +N (a +N c *N a)) +N c) (equalityCommutative (productDistributes c b (a *N b)))))) (applyEquality (_+N c) (equalityCommutative (productDistributes (succ c) (succ a *N b) a))))
*ZAssociative (nonneg (succ a)) (negSucc b) (negSucc x) = applyEquality nonneg ans
  where
    ans : succ a *N (succ b *N succ x) ≡ succ ((succ a *N b) +N a) *N succ x
    ans rewrite Semiring.commutative ℕSemiring (succ a *N b) a | multiplicationNIsCommutative (succ a) b = transitivity (Semiring.*Associative ℕSemiring (succ a) (succ b) (succ x)) (applyEquality (_*N succ x) {succ a *N succ b} {succ b *N succ a} (multiplicationNIsCommutative (succ a) (succ b)))
*ZAssociative (negSucc a) (nonneg zero) c rewrite *ZZeroLeft c = refl
*ZAssociative (negSucc a) (nonneg (succ b)) (nonneg zero) rewrite multiplicationNIsCommutative b 0 = refl
*ZAssociative (negSucc a) (nonneg (succ b)) (nonneg (succ c)) = applyEquality negSucc ans
  where
    ans2 : (d : ℕ) → ((succ b *N d) *N a) +N b *N d ≡ d *N ((succ b *N a) +N b)
    ans2 d = transitivity (transitivity (applyEquality (((d +N b *N d) *N a) +N_) (multiplicationNIsCommutative b d)) (applyEquality (_+N d *N b) (transitivity (applyEquality (_*N a) {d +N b *N d} {d *N succ b} (multiplicationNIsCommutative (succ b) d)) (equalityCommutative (Semiring.*Associative ℕSemiring d (succ b) a))))) (equalityCommutative (Semiring.+DistributesOver* ℕSemiring d (succ b *N a) b))
    ans : (succ (c +N b *N succ c) *N a) +N (c +N b *N succ c) ≡ (succ c *N ((succ b *N a) +N b)) +N c
    ans rewrite Semiring.commutative ℕSemiring c (b *N succ c) | Semiring.+Associative ℕSemiring (succ (b *N succ c +N c) *N a) (b *N succ c) c | Semiring.commutative ℕSemiring (b *N succ c) c = applyEquality (_+N c) (ans2 (succ c))
*ZAssociative (negSucc a) (nonneg (succ b)) (negSucc c) = applyEquality nonneg ans
  where
    ans : succ a *N ((succ ((succ b) *N c)) +N b) ≡ (succ (succ b *N a) +N b) *N succ c
    ans rewrite Semiring.commutative ℕSemiring (succ b *N a) b | multiplicationNIsCommutative (succ b) a = transitivity (applyEquality (succ a *N_) (applyEquality succ (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring c (b *N c) b)) (applyEquality (c +N_) (transitivity (transitivity (Semiring.commutative ℕSemiring (b *N c) b) (applyEquality (b +N_) (multiplicationNIsCommutative b c))) (multiplicationNIsCommutative (succ c) b)))))) (Semiring.*Associative ℕSemiring (succ a) (succ b) (succ c))
*ZAssociative (negSucc a) (negSucc b) (nonneg zero) rewrite Semiring.productZeroRight ℕSemiring (b +N a *N succ b) = refl
*ZAssociative (negSucc a) (negSucc b) (nonneg (succ x)) = applyEquality nonneg (transitivity (applyEquality (succ a *N_) ans) (Semiring.*Associative ℕSemiring (succ a) (succ b) (succ x)))
  where
    ans : succ ((succ x *N b) +N x) ≡ (succ b *N succ x)
    ans rewrite Semiring.commutative ℕSemiring (succ x *N b) x | multiplicationNIsCommutative (succ x) b = refl
*ZAssociative (negSucc a) (negSucc b) (negSucc x) = applyEquality negSucc t
  where
    l1 : (a b c d e f g : ℕ) → (a +N b) +N d ≡ e +N (f +N g) → (a +N b) +N (c +N d) ≡ (c +N e) +N (f +N g)
    l1 a b c d e f g pr rewrite Semiring.commutative ℕSemiring c d | Semiring.+Associative ℕSemiring (a +N b) d c | pr | Semiring.commutative ℕSemiring (e +N (f +N g)) c | Semiring.+Associative ℕSemiring c e (f +N g) = refl
    v : (((succ b) *N succ x) *N a) ≡ (succ x) *N (a *N succ b)
    v = transitivity (applyEquality (_*N a) (multiplicationNIsCommutative (succ b) (succ x))) (transitivity (equalityCommutative (Semiring.*Associative ℕSemiring (succ x) (succ b) a)) (applyEquality (succ x *N_) (multiplicationNIsCommutative (succ b) a)))
    u : (a +N (x +N b *N succ x) *N a) +N b *N succ x ≡ (b +N a *N succ b) *N x +N (b +N a *N succ b)
    u = transitivity (transitivity (transitivity (Semiring.commutative ℕSemiring (a +N (x +N b *N succ x) *N a) (b *N succ x)) (transitivity (applyEquality (_+N (a +N (x +N b *N succ x) *N a)) (multiplicationNIsCommutative b (succ x))) (transitivity (applyEquality ((b +N x *N b) +N_) v) (equalityCommutative (productDistributes (succ x) b (a *N succ b)))))) (applyEquality ((b +N a *N succ b) +N_) (multiplicationNIsCommutative x (b +N a *N succ b)))) (Semiring.commutative ℕSemiring (b +N a *N succ b) ((b +N a *N succ b) *N x))
    t : (a +N (x +N b *N succ x) *N a) +N (x +N b *N succ x) ≡ (x +N (b +N a *N succ b) *N x) +N (b +N a *N succ b)
    t = l1 a ((x +N b *N succ x) *N a) x (b *N succ x) ((b +N (a *N succ b)) *N x) b (a *N succ b) u

multLemma : (a b : ℕ) → a *N succ b ≡ a *N b +N a
multLemma a b rewrite multiplicationNIsCommutative a (succ b) | Semiring.commutative ℕSemiring a (b *N a) | multiplicationNIsCommutative a b = refl

negSucc+Nonneg : (a b : ℕ) → negSucc a ≡ negSucc (a +N b) +Z nonneg b
negSucc+Nonneg zero zero = refl
negSucc+Nonneg zero (succ b) = negSucc+Nonneg zero b
negSucc+Nonneg (succ a) zero rewrite Semiring.commutative ℕSemiring a 0 = refl
negSucc+Nonneg (succ a) (succ b) rewrite Semiring.commutative ℕSemiring a (succ b) | Semiring.commutative ℕSemiring b a = negSucc+Nonneg (succ a) b

distLemma : (a b : ℕ) →  negSucc a *Z nonneg b ≡ negSucc ((a +N b *N a) +N b) +Z nonneg (succ a)
distLemma a b rewrite Semiring.commutative ℕSemiring (a +N b *N a) b | Semiring.commutative ℕSemiring a (b *N a) | Semiring.+Associative ℕSemiring b (b *N a) a = transitivity u (transitivity (equalityCommutative (+ZAssociative (negSucc ((b +N b *N a) +N a)) (nonneg a) (nonneg 1))) (applyEquality ((negSucc ((b +N b *N a) +N a)) +Z_) {nonneg a +Z nonneg 1} {nonneg (succ a)} (+ZCommutative (nonneg a) (nonneg 1))))
  where
    v : (a b : ℕ) → negSucc a *Z nonneg b ≡ (negSucc (b +N b *N a)) +Z nonneg 1
    v zero zero = refl
    v zero (succ b) rewrite Semiring.productZeroRight ℕSemiring b = applyEquality negSucc (equalityCommutative (Semiring.sumZeroRight ℕSemiring b))
    v (succ a) zero = refl
    v (succ a) (succ b) = applyEquality negSucc (Semiring.commutative ℕSemiring (succ (a +N b *N succ a)) b)
    u : negSucc a *Z nonneg b ≡ (negSucc ((b +N b *N a) +N a) +Z nonneg a) +Z nonneg 1
    u = transitivity (v a b) (applyEquality (_+Z nonneg 1) (negSucc+Nonneg (b +N b *N a) a))

*ZDistributesOver+Z : (a b c : ℤ) → a *Z (b +Z c) ≡ (a *Z b) +Z (a *Z c)
*ZDistributesOver+Z (nonneg zero) b c rewrite *ZZeroLeft (b +Z c) | *ZZeroLeft b | *ZZeroLeft c = refl
*ZDistributesOver+Z (nonneg (succ a)) (nonneg zero) (nonneg c) rewrite Semiring.productZeroRight ℕSemiring a = refl
*ZDistributesOver+Z (nonneg (succ a)) (nonneg (succ b)) (nonneg c) = applyEquality nonneg (productDistributes (succ a) (succ b) c)
*ZDistributesOver+Z (nonneg (succ a)) (nonneg zero) (negSucc c) rewrite Semiring.productZeroRight ℕSemiring a = refl
*ZDistributesOver+Z (nonneg (succ a)) (nonneg (succ b)) (negSucc zero) rewrite Semiring.productZeroRight ℕSemiring a = t a
  where
    t : (a : ℕ) → nonneg (succ a *N b) ≡ nonneg (succ a *N succ b) +Z negSucc a
    t zero = refl
    t (succ a) = transitivity (+Zinherits b (b +N a *N b)) (transitivity (applyEquality (nonneg b +Z_) (t a)) (transitivity (+ZAssociative (nonneg b) (nonneg (succ (b +N a *N succ b))) (negSucc a)) (applyEquality (_+Z negSucc a) {nonneg b +Z nonneg (succ (b +N a *N succ b))} {nonneg (b +N succ (b +N a *N succ b))} (equalityCommutative (+Zinherits b _)))))
*ZDistributesOver+Z (nonneg (succ a)) (nonneg (succ x)) (negSucc (succ b)) = transitivity (applyEquality ((nonneg (succ a)) *Z_) (+ZCommutative (nonneg x) (negSucc b))) (transitivity (transitivity (*ZDistributesOver+Z (nonneg (succ a)) (negSucc b) (nonneg x)) t) (+ZCommutative (negSucc ((b +N a *N succ b) +N a)) (nonneg (x +N a *N succ x))))
  where
    t : negSucc ((b +N a *N b) +N a) +Z nonneg (x +N a *N x) ≡ negSucc ((b +N a *N succ b) +N a) +Z nonneg (x +N a *N succ x)
    t rewrite multLemma a x | multLemma a b | Semiring.+Associative ℕSemiring x (a *N x) a | Semiring.+Associative ℕSemiring b (a *N b) a | Semiring.commutative ℕSemiring (x +N a *N x) a | +Zinherits a (x +N a *N x) | +ZAssociative (negSucc (((b +N a *N b) +N a) +N a)) (nonneg a) (nonneg (x +N a *N x)) = applyEquality (_+Z nonneg (x +N a *N x)) {negSucc ((b +N a *N b) +N a)} {negSucc (((b +N a *N b) +N a) +N a) +Z nonneg a} (negSucc+Nonneg ((b +N a *N b) +N a) a)
*ZDistributesOver+Z (nonneg (succ a)) (negSucc b) (nonneg zero) rewrite Semiring.productZeroRight ℕSemiring a = refl
*ZDistributesOver+Z (nonneg (succ a)) (negSucc zero) (nonneg (succ x)) rewrite Semiring.productZeroRight ℕSemiring a = t a x
  where
    t : (a x : ℕ) → nonneg (succ a *N x) ≡ negSucc a +Z nonneg (succ a *N succ x)
    t zero x = refl
    t (succ a) x with t a x
    ... | bl rewrite +Zinherits x (a *N x) | +Zinherits x (x +N a *N x) = transitivity (transitivity (applyEquality (nonneg x +Z_) (+Zinherits x (a *N x))) (+ZCommutative (nonneg x) (nonneg x +Z nonneg (a *N x)))) (transitivity (applyEquality (_+Z nonneg x) bl) (transitivity (equalityCommutative (+ZAssociative (negSucc a) (nonneg (succ x +N a *N succ x)) (nonneg x))) (applyEquality (λ i → negSucc a +Z nonneg i) {succ (x +N a *N succ x) +N x} {x +N succ (x +N a *N succ x)} (Semiring.commutative ℕSemiring (succ (x +N a *N succ x)) x))))
*ZDistributesOver+Z (nonneg (succ a)) (negSucc (succ b)) (nonneg (succ x)) = transitivity (*ZDistributesOver+Z (nonneg (succ a)) (negSucc b) (nonneg x)) t
  where
    t : negSucc ((b +N a *N b) +N a) +Z nonneg (x +N a *N x) ≡ negSucc ((b +N a *N succ b) +N a) +Z nonneg (x +N a *N succ x)
    t rewrite multLemma a x | multLemma a b | Semiring.+Associative ℕSemiring x (a *N x) a | Semiring.+Associative ℕSemiring b (a *N b) a | Semiring.commutative ℕSemiring (x +N a *N x) a | +Zinherits a (x +N a *N x) | +ZAssociative (negSucc (((b +N a *N b) +N a) +N a)) (nonneg a) (nonneg (x +N a *N x)) = applyEquality (_+Z nonneg (x +N a *N x)) {negSucc ((b +N a *N b) +N a)} {negSucc (((b +N a *N b) +N a) +N a) +Z nonneg a} (negSucc+Nonneg ((b +N a *N b) +N a) a)
*ZDistributesOver+Z (nonneg (succ a)) (negSucc b) (negSucc x) = applyEquality negSucc (transitivity (applyEquality (_+N a) (transitivity (productDistributes (succ a) (succ b) x) (applyEquality (_+N (x +N a *N x)) {succ b +N a *N succ b} {succ (b +N a *N b) +N a} (applyEquality succ u)))) (equalityCommutative (Semiring.+Associative ℕSemiring (succ ((b +N a *N b) +N a)) (succ a *N x) a)))
  where
    u : b +N a *N succ b ≡ (succ a *N b) +N a
    u rewrite multiplicationNIsCommutative a (succ b) | Semiring.commutative ℕSemiring a (b *N a) | multiplicationNIsCommutative b a = Semiring.+Associative ℕSemiring b (a *N b) a
*ZDistributesOver+Z (negSucc a) (nonneg zero) (nonneg x) = refl
*ZDistributesOver+Z (negSucc a) (nonneg zero) (negSucc x) = refl
*ZDistributesOver+Z (negSucc a) (nonneg (succ b)) (nonneg zero) rewrite Semiring.commutative ℕSemiring b 0 = refl
*ZDistributesOver+Z (negSucc a) (nonneg (succ b)) (nonneg (succ c)) = applyEquality negSucc t
  where
    v : a *N b +N a *N succ c ≡ c *N a +N (a +N b *N a)
    v rewrite multiplicationNIsCommutative b a | Semiring.+Associative ℕSemiring (c *N a) a (a *N b) | Semiring.commutative ℕSemiring (c *N a +N a) (a *N b) | Semiring.commutative ℕSemiring (c *N a) a = applyEquality (λ i → a *N b +N i) (transitivity (multLemma a c) (transitivity (Semiring.commutative ℕSemiring (a *N c) a) (applyEquality (a +N_) (multiplicationNIsCommutative a c))))
    u : (a +N (b +N succ c) *N a) +N b ≡ (a +N c *N a) +N ((a +N b *N a) +N b)
    u rewrite Semiring.+Associative ℕSemiring (a +N c *N a) (a +N b *N a) b | (equalityCommutative (Semiring.+Associative ℕSemiring a (c *N a) (a +N b *N a))) = applyEquality (λ i → (a +N i) +N b) (transitivity (multiplicationNIsCommutative (b +N succ c) a) (transitivity (productDistributes a b (succ c)) v))
    t : (a +N (b +N succ c) *N a) +N (b +N succ c) ≡ succ (((a +N b *N a) +N b) +N ((a +N c *N a) +N c))
    t rewrite Semiring.+Associative ℕSemiring ((a +N (b +N succ c) *N a)) b (succ c) | Semiring.commutative ℕSemiring ((a +N b *N a) +N b) ((a +N c *N a) +N c) | Semiring.commutative ℕSemiring (a +N c *N a) c | equalityCommutative (Semiring.+Associative ℕSemiring (succ c) (a +N c *N a) ((a +N b *N a) +N b)) | Semiring.commutative ℕSemiring (succ c) ((a +N c *N a) +N ((a +N b *N a) +N b)) = applyEquality (_+N succ c) u
*ZDistributesOver+Z (negSucc a) (nonneg (succ b)) (negSucc zero) rewrite Semiring.productOneRight ℕSemiring a = distLemma a b
*ZDistributesOver+Z (negSucc a) (nonneg (succ b)) (negSucc (succ c)) = transitivity (*ZDistributesOver+Z (negSucc a) (nonneg b) (negSucc c)) (transitivity (applyEquality (_+Z nonneg (succ (c +N a *N succ c))) (distLemma a b)) (transitivity (equalityCommutative (+ZAssociative (negSucc ((a +N b *N a) +N b)) (nonneg (succ a)) (nonneg (succ (c +N a *N succ c))))) (applyEquality (negSucc ((a +N b *N a) +N b) +Z_) {nonneg (succ (a +N succ (c +N a *N succ c)))} {nonneg (succ (succ (c +N a *N succ (succ c))))} (applyEquality nonneg (t (succ a) (succ c))))))
  where
    t : (x y : ℕ) → x +N x *N y ≡ x *N succ y
    t x y = transitivity (Semiring.commutative ℕSemiring x (x *N y)) (equalityCommutative (multLemma x y))
*ZDistributesOver+Z (negSucc a) (negSucc b) (nonneg zero) rewrite Semiring.commutative ℕSemiring (b +N a *N succ b) 0 = refl
*ZDistributesOver+Z (negSucc a) (negSucc zero) (nonneg (succ b)) = transitivity (distLemma a b) (transitivity (+ZCommutative (negSucc ((a +N b *N a) +N b)) (nonneg (succ a))) (applyEquality (λ i → nonneg (succ i) +Z negSucc ((a +N b *N a) +N b)) (equalityCommutative (Semiring.productOneRight ℕSemiring a))))
*ZDistributesOver+Z (negSucc a) (negSucc (succ c)) (nonneg (succ b)) = transitivity (applyEquality (negSucc a *Z_) (+ZCommutative (negSucc c) (nonneg b))) (transitivity (transitivity (*ZDistributesOver+Z (negSucc a) (nonneg b) (negSucc c)) (transitivity (applyEquality (_+Z nonneg (succ (c +N a *N succ c))) (distLemma a b)) (transitivity (equalityCommutative (+ZAssociative (negSucc ((a +N b *N a) +N b)) (nonneg (succ a)) (nonneg (succ (c +N a *N succ c))))) (applyEquality (negSucc ((a +N b *N a) +N b) +Z_) {nonneg (succ (a +N succ (c +N a *N succ c)))} {nonneg (succ (succ (c +N a *N succ (succ c))))} (applyEquality nonneg (t (succ a) (succ c))))))) (+ZCommutative (negSucc ((a +N b *N a) +N b)) (nonneg (succ (succ (c +N a *N succ (succ c)))))))
  where
    t : (x y : ℕ) → x +N x *N y ≡ x *N succ y
    t x y = transitivity (Semiring.commutative ℕSemiring x (x *N y)) (equalityCommutative (multLemma x y))
*ZDistributesOver+Z (negSucc a) (negSucc b) (negSucc c) = applyEquality nonneg (transitivity (applyEquality (λ i → succ a *N (succ i)) (transitivity (applyEquality succ (Semiring.commutative ℕSemiring b c)) (Semiring.commutative ℕSemiring (succ c) b))) (productDistributes (succ a) (succ b) (succ c)))

ℤRing : Ring (reflSetoid ℤ) _+Z_ _*Z_
Ring.additiveGroup ℤRing = ℤGroup
Ring.*WellDefined ℤRing refl refl = refl
Ring.1R ℤRing = nonneg 1
Ring.groupIsAbelian ℤRing {a} {b} = +ZCommutative a b
Ring.*Associative ℤRing {a} {b} {c} = *ZAssociative a b c
Ring.*Commutative ℤRing {a} {b} = *ZCommutative a b
Ring.*DistributesOver+ ℤRing {a} {b} {c} = *ZDistributesOver+Z a b c
Ring.identIsIdent ℤRing {a} = *ZleftIdent a
