{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Integers.Definition
open import Semirings.Definition
open import Groups.Abelian.Definition
open import Groups.Definition
open import Setoids.Setoids

module Numbers.Integers.Addition where

infix 15 _+Z_
_+Z_ : ℤ → ℤ → ℤ
nonneg zero +Z b = b
nonneg (succ x) +Z nonneg y = nonneg (succ x +N y)
nonneg (succ x) +Z negSucc zero = nonneg x
nonneg (succ x) +Z negSucc (succ y) = nonneg x +Z negSucc y
negSucc x +Z nonneg zero = negSucc x
negSucc zero +Z nonneg (succ y) = nonneg y
negSucc (succ x) +Z nonneg (succ y) = negSucc x +Z nonneg y
negSucc x +Z negSucc y = negSucc (succ x +N y)

+Zinherits : (a b : ℕ) → nonneg (a +N b) ≡ (nonneg a) +Z (nonneg b)
+Zinherits zero b = refl
+Zinherits (succ a) b = refl

+ZCommutative : (a b : ℤ) → a +Z b ≡ b +Z a
+ZCommutative (nonneg zero) (nonneg zero) = refl
+ZCommutative (nonneg zero) (nonneg (succ y)) = applyEquality (λ i → nonneg (succ i)) (Semiring.commutative ℕSemiring 0 y)
+ZCommutative (nonneg (succ x)) (nonneg zero) = applyEquality (λ i → nonneg (succ i)) (Semiring.commutative ℕSemiring x 0)
+ZCommutative (nonneg (succ x)) (nonneg (succ y)) = applyEquality (λ i → nonneg (succ i)) (transitivity (Semiring.commutative ℕSemiring x (succ y)) (transitivity (applyEquality succ (Semiring.commutative ℕSemiring y x)) (Semiring.commutative ℕSemiring (succ x) y)))
+ZCommutative (nonneg zero) (negSucc y) = refl
+ZCommutative (nonneg (succ x)) (negSucc zero) = refl
+ZCommutative (nonneg (succ x)) (negSucc (succ y)) = +ZCommutative (nonneg x) (negSucc y)
+ZCommutative (negSucc x) (nonneg zero) = refl
+ZCommutative (negSucc zero) (nonneg (succ y)) = refl
+ZCommutative (negSucc (succ x)) (nonneg (succ y)) = +ZCommutative (negSucc x) (nonneg y)
+ZCommutative (negSucc x) (negSucc y) = applyEquality (λ i → negSucc (succ i)) (Semiring.commutative ℕSemiring x y)

+ZAssociative : (a b c : ℤ) → a +Z (b +Z c) ≡ (a +Z b) +Z c
+ZAssociative (nonneg zero) (nonneg b) (nonneg c) = refl
+ZAssociative (nonneg (succ a)) (nonneg zero) (nonneg c) rewrite Semiring.commutative ℕSemiring a 0 = refl
+ZAssociative (nonneg (succ a)) (nonneg (succ b)) (nonneg c) = applyEquality (λ i → nonneg (succ i)) (Semiring.+Associative ℕSemiring a (succ b) c)
+ZAssociative (nonneg zero) (nonneg b) (negSucc c) = refl
+ZAssociative (nonneg (succ a)) (nonneg zero) (negSucc c) rewrite Semiring.sumZeroRight ℕSemiring a = refl
+ZAssociative (nonneg (succ a)) (nonneg (succ b)) (negSucc zero) = applyEquality nonneg (transitivity (applyEquality succ (Semiring.commutative ℕSemiring a b)) (Semiring.commutative ℕSemiring (succ b) a))
+ZAssociative (nonneg (succ a)) (nonneg (succ b)) (negSucc (succ c)) = transitivity (+ZAssociative (nonneg (succ a)) (nonneg b) (negSucc c)) (applyEquality (λ i → nonneg i +Z negSucc c) (transitivity (applyEquality succ (Semiring.commutative ℕSemiring a b)) (Semiring.commutative ℕSemiring (succ b) a)))
+ZAssociative (nonneg zero) (negSucc b) c = refl
+ZAssociative (nonneg (succ a)) (negSucc zero) (nonneg zero) = +ZCommutative (nonneg 0) (nonneg a)
+ZAssociative (nonneg (succ a)) (negSucc zero) (nonneg (succ c)) = transitivity (applyEquality nonneg (transitivity (applyEquality succ (Semiring.commutative ℕSemiring a c)) (Semiring.commutative ℕSemiring (succ c) a))) (+Zinherits a (succ c))
+ZAssociative (nonneg (succ a)) (negSucc zero) (negSucc c) = refl
+ZAssociative (nonneg (succ a)) (negSucc (succ b)) (nonneg zero) = +ZCommutative (nonneg 0) _
+ZAssociative (nonneg (succ a)) (negSucc (succ b)) (nonneg (succ c)) = transitivity (applyEquality (nonneg (succ a) +Z_) (+ZCommutative (negSucc b) (nonneg c))) (transitivity (+ZAssociative (nonneg (succ a)) (nonneg c) (negSucc b)) (transitivity (transitivity (transitivity (transitivity (applyEquality (λ i → nonneg (succ i) +Z negSucc b) (Semiring.commutative ℕSemiring a c)) (+ZCommutative (nonneg (succ (c +N a))) (negSucc b))) (applyEquality (negSucc b +Z_) (+ZCommutative (nonneg (succ c)) (nonneg a)))) (+ZAssociative (negSucc b) (nonneg a) (nonneg (succ c)))) (applyEquality (_+Z nonneg (succ c)) (+ZCommutative (negSucc b) (nonneg a)))))
+ZAssociative (nonneg (succ a)) (negSucc (succ b)) (negSucc c) = +ZAssociative (nonneg a) (negSucc b) (negSucc c)
+ZAssociative (negSucc a) (nonneg zero) c = refl
+ZAssociative (negSucc zero) (nonneg (succ b)) (nonneg c) = +Zinherits b c
+ZAssociative (negSucc zero) (nonneg (succ b)) (negSucc zero) = +ZCommutative (negSucc 0) (nonneg b)
+ZAssociative (negSucc zero) (nonneg (succ b)) (negSucc (succ c)) = transitivity (+ZCommutative (negSucc 0) (nonneg b +Z negSucc c)) (transitivity (equalityCommutative (+ZAssociative (nonneg b) (negSucc c) (negSucc 0))) (applyEquality (λ i → nonneg b +Z negSucc (succ i)) (Semiring.sumZeroRight ℕSemiring c)))
+ZAssociative (negSucc (succ a)) (nonneg (succ b)) (nonneg zero) = transitivity (applyEquality (λ i → negSucc a +Z (nonneg i)) (Semiring.sumZeroRight ℕSemiring b)) (+ZCommutative (nonneg 0) (negSucc a +Z nonneg b))
+ZAssociative (negSucc (succ a)) (nonneg (succ b)) (nonneg (succ c)) = transitivity (applyEquality (negSucc a +Z_) (+Zinherits b (succ c))) (+ZAssociative (negSucc a) (nonneg b) (nonneg (succ c)))
+ZAssociative (negSucc (succ a)) (nonneg (succ b)) (negSucc zero) = transitivity (+ZCommutative (negSucc (succ a)) (nonneg b)) (transitivity (transitivity (applyEquality (λ i → nonneg b +Z negSucc (succ i)) (equalityCommutative (Semiring.sumZeroRight ℕSemiring a))) (+ZAssociative (nonneg b) (negSucc a) (negSucc 0))) (applyEquality (_+Z negSucc 0) (+ZCommutative (nonneg b) (negSucc a))))
+ZAssociative (negSucc (succ a)) (nonneg (succ b)) (negSucc (succ c)) = transitivity (+ZCommutative (negSucc (succ a)) (nonneg b +Z negSucc c)) (transitivity (transitivity (equalityCommutative (+ZAssociative (nonneg b) (negSucc c) (negSucc (succ a)))) (transitivity (applyEquality (λ i → nonneg b +Z negSucc i) (Semiring.commutative ℕSemiring (succ c) (succ a))) (+ZAssociative (nonneg b) (negSucc a) (negSucc (succ c))))) (applyEquality (_+Z negSucc (succ c)) (+ZCommutative (nonneg b) (negSucc a))))
+ZAssociative (negSucc a) (negSucc b) (nonneg zero) = refl
+ZAssociative (negSucc a) (negSucc zero) (nonneg (succ c)) = applyEquality (λ i → negSucc i +Z nonneg c) (Semiring.commutative ℕSemiring 0 a)
+ZAssociative (negSucc a) (negSucc (succ b)) (nonneg (succ c)) = transitivity (+ZAssociative (negSucc a) (negSucc b) (nonneg c)) (applyEquality (λ i → negSucc i +Z nonneg c) (transitivity (applyEquality succ (Semiring.commutative ℕSemiring a b)) (Semiring.commutative ℕSemiring (succ b) a)))
+ZAssociative (negSucc a) (negSucc b) (negSucc c) = applyEquality (λ i → negSucc (succ i)) (transitivity (Semiring.+Associative ℕSemiring a (succ b) c) (applyEquality (_+N c) (transitivity (Semiring.commutative ℕSemiring a (succ b)) (applyEquality succ (Semiring.commutative ℕSemiring b a)))))

additiveInverseExists : (a : ℕ) → (negSucc a +Z nonneg (succ a)) ≡ nonneg 0
additiveInverseExists zero = refl
additiveInverseExists (succ a) = additiveInverseExists a

additiveInverse : (a : ℤ) → ℤ
additiveInverse (nonneg zero) = nonneg 0
additiveInverse (nonneg (succ x)) = negSucc x
additiveInverse (negSucc x) = nonneg (succ x)

ℤGroup : Group (reflSetoid ℤ) (_+Z_)
Group.+WellDefined ℤGroup refl refl = refl
Group.0G ℤGroup = nonneg 0
Group.inverse ℤGroup = additiveInverse
Group.+Associative ℤGroup {a} {b} {c} = +ZAssociative a b c
Group.identRight ℤGroup {nonneg zero} = refl
Group.identRight ℤGroup {nonneg (succ x)} = applyEquality (λ i → nonneg (succ i)) (Semiring.commutative ℕSemiring x 0)
Group.identRight ℤGroup {negSucc x} = refl
Group.identLeft ℤGroup = refl
Group.invLeft ℤGroup {nonneg zero} = refl
Group.invLeft ℤGroup {nonneg (succ x)} = additiveInverseExists x
Group.invLeft ℤGroup {negSucc x} = transitivity (+ZCommutative (nonneg (succ x)) (negSucc x)) (additiveInverseExists x)
Group.invRight ℤGroup {nonneg zero} = refl
Group.invRight ℤGroup {nonneg (succ x)} = transitivity (+ZCommutative (nonneg (succ x)) (negSucc x)) (additiveInverseExists x)
Group.invRight ℤGroup {negSucc x} = additiveInverseExists x

ℤAbGrp : AbelianGroup ℤGroup
ℤAbGrp = record { commutative = λ {a} {b} → +ZCommutative a b }
