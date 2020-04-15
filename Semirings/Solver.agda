{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Semirings.Definition

module Semirings.Solver {a : _} {A : Set a} {Zero One : A} {_+_ : A → A → A} {_*_ : A → A → A} (S : Semiring Zero One _+_ _*_) (comm : (a b : A) → a * b ≡ b * a) where

open Semiring S

-- You can see how to use the solver in LectureNotes/NumbersAndSets/Lecture1.agda.

data Expr : Set a where
  const : A → Expr
  zero : Expr
  succ : Expr → Expr
  plus : Expr → Expr → Expr
  times : Expr → Expr → Expr

-- TODO: do this in distinct phases. (Work out what those phases are.)
-- Expose those phases to the user so that they can choose which tactics to use.
-- Phases:
--  * In any expression which is all sums, extract all consts out to the front
--  * In any expression which is all sums, extract all the succs to the front

eval : Expr → A
eval (const k) = k
eval zero = Zero
eval (succ e) = One + (eval e)
eval (plus x y) = (eval x) + (eval y)
eval (times x y) = (eval x) * (eval y)

simplePlus : Expr → Expr → Expr
simplePlus (const x) (const y) = plus (const x) (const y)
simplePlus (const x) zero = const x
simplePlus (const x) (succ b) = succ (plus (const x) b)
simplePlus (const x) (plus a b) = plus (const x) (plus a b)
simplePlus (const x) (times a b) = plus (const x) (times a b)
simplePlus zero b = b
simplePlus (succ a) (const x) = succ (plus (const x) a)
simplePlus (succ a) zero = succ a
simplePlus (succ a) (succ b) = succ (succ (plus a b))
simplePlus (succ a) (plus b c) = succ (plus a (plus b c))
simplePlus (succ a) (times b c) = succ (plus a (times b c))
simplePlus (plus a b) (const x) = plus (const x) (plus a b)
simplePlus (plus a b) zero = plus a b
simplePlus (plus a b) (succ c) = succ (plus a (plus b c))
simplePlus (plus a b) (plus c d) = plus a (plus b (plus c d))
simplePlus (plus a b) (times c d) = plus a (plus b (times c d))
simplePlus (times a b) (const x) = plus (const x) (times a b)
simplePlus (times a b) zero = times a b
simplePlus (times a b) (succ c) = succ (plus (times a b) c)
simplePlus (times a b) (plus c d) = plus (times a b) (plus c d)
simplePlus (times a b) (times c d) = plus (times a b) (times c d)

private
  lemma : (a b c : A) → a + (b + c) ≡ b + (a + c)
  lemma a b c rewrite commutative a (b + c) | equalityCommutative (+Associative b c a) = applyEquality (b +_) (commutative _ _)

simplePlusIsPlus : (a b : Expr) → eval (simplePlus a b) ≡ eval (plus a b)
simplePlusIsPlus (const x) (const x₁) = refl
simplePlusIsPlus (const x) zero rewrite Semiring.sumZeroRight S x = refl
simplePlusIsPlus (const x) (succ b) = lemma One x (eval b)
simplePlusIsPlus (const x) (plus b c) = refl
simplePlusIsPlus (const x) (times b c) = refl
simplePlusIsPlus zero b = equalityCommutative (sumZeroLeft (eval b))
simplePlusIsPlus (succ a) (const x) rewrite lemma One x (eval a) = commutative x _
simplePlusIsPlus (succ a) zero = equalityCommutative (sumZeroRight _)
simplePlusIsPlus (succ a) (succ b) rewrite lemma (One + eval a) One (eval b) = applyEquality (One +_) (+Associative One _ _)
simplePlusIsPlus (succ a) (plus b c) = +Associative _ _ _
simplePlusIsPlus (succ a) (times b c) = +Associative _ _ _
simplePlusIsPlus (plus a b) (const x) = commutative x _
simplePlusIsPlus (plus a b) zero = equalityCommutative (sumZeroRight _)
simplePlusIsPlus (plus a b) (succ c) rewrite lemma (eval a + eval b) One (eval c) = applyEquality (One +_) (+Associative _ _ _)
simplePlusIsPlus (plus a b) (plus c d) = +Associative (eval a) _ _
simplePlusIsPlus (plus a b) (times c d) = +Associative _ _ _
simplePlusIsPlus (times a b) (const x) = commutative x _
simplePlusIsPlus (times a b) zero = equalityCommutative (sumZeroRight _)
simplePlusIsPlus (times a b) (succ c) rewrite lemma One (eval a * eval b) (eval c) = refl
simplePlusIsPlus (times a b) (plus c d) = refl
simplePlusIsPlus (times a b) (times c d) = refl

simplify : Expr → Expr
simplify (const k) = const k
simplify zero = zero
simplify (succ e) = succ (simplify e)
simplify (plus (const k) (const x)) = simplePlus (const k) (const x)
simplify (plus (const k) zero) = simplify (const k)
simplify (plus (const k) (succ expr)) = succ (simplify (plus (const k) expr))
simplify (plus (const k) (plus x y)) = simplePlus (const k) (simplify (plus x y))
simplify (plus (const k) (times x y)) = simplePlus (const k) (simplify (times x y))
simplify (plus zero expr2) = simplify expr2
simplify (plus (succ expr1) expr2) = succ (simplify (plus expr1 expr2))
simplify (plus (plus expr1 expr3) zero) = simplify (plus expr1 expr3)
simplify (plus (plus expr1 expr3) (const k)) = simplePlus (const k) (simplify (plus expr1 expr3))
simplify (plus (plus expr1 expr3) (succ expr2)) = succ (simplePlus (simplify (plus expr1 expr3)) (simplify expr2))
simplify (plus (plus expr1 expr3) (plus expr2 expr4)) = simplePlus (simplify (plus expr1 expr3)) (simplify (plus expr2 expr4))
simplify (plus (plus expr1 expr3) (times expr2 expr4)) = simplePlus (simplify (plus expr1 expr3)) (simplify (times expr2 expr4))
simplify (plus (times expr1 expr3) (const k)) = simplePlus (const k) (simplify (times expr1 expr3))
simplify (plus (times expr1 expr3) zero) = times (simplify expr1) (simplify expr3)
simplify (plus (times expr1 expr3) (succ expr2)) = succ (simplePlus (simplify (times expr1 expr3)) (simplify expr2))
simplify (plus (times expr1 expr3) (plus expr2 expr4)) = simplePlus (simplify (times expr1 expr3)) (simplify (plus expr2 expr4))
simplify (plus (times expr1 expr3) (times expr2 expr4)) = simplePlus (simplify (times expr1 expr3)) (simplify (times expr2 expr4))
simplify (times (const k) (const x)) = times (const k) (const x)
simplify (times (const k) zero) = zero
simplify (times (const k) (succ zero)) = const k
simplify (times (const k) (succ (const y))) = simplePlus (const k) (times (const k) (const y))
simplify (times (const k) (succ (plus a b))) = simplePlus (const k) (simplify (times (const k) (plus a b)))
simplify (times (const k) (succ (times a b))) = simplePlus (const k) (simplify (times (const k) (times a b)))
simplify (times (const k) (succ (succ x))) = simplePlus (const k) (simplify (times (const k) (succ x)))
simplify (times (const k) (plus expr2 expr3)) = simplePlus (simplify (times (const k) (expr2))) (simplify (times (const k) expr3))
simplify (times (const k) (times expr2 expr3)) = times (const k) (simplify (times expr2 expr3))
simplify (times zero expr2) = zero
simplify (times (succ zero) expr2) = simplify expr2
simplify (times (succ (succ expr1)) expr2) = simplePlus (simplify expr2) (simplify (times (succ expr1) expr2))
simplify (times (succ (plus expr1 expr3)) (const k)) = times (const k) (simplify (succ (plus expr1 expr3)))
simplify (times (succ (plus expr1 expr3)) zero) = zero
simplify (times (succ (plus expr1 expr3)) (succ expr2)) = succ (simplePlus (simplify (times expr1 expr2)) (simplePlus (simplify (times expr3 expr2)) (simplePlus expr2 (simplify (plus expr1 expr3)))))
simplify (times (succ (plus expr1 expr3)) (plus expr2 expr4)) = times (simplify (succ (plus expr1 expr3))) (simplify (plus expr2 expr4))
simplify (times (succ (plus expr1 expr3)) (times expr2 expr4)) = times (simplify (succ (plus expr1 expr3))) (simplify (times expr2 expr4))
simplify (times (succ (const k)) (const x)) = simplePlus (const x) (times (const k) (const x))
simplify (times (succ (const k)) zero) = zero
simplify (times (succ (const k)) (succ (const x))) = succ (simplePlus (const k) (simplePlus (const x) (simplify (times (const k) (const x)))))
simplify (times (succ (const k)) (succ zero)) = succ (const k)
simplify (times (succ (const k)) (succ (succ expr2))) = succ (simplePlus (const k) (simplePlus (simplify (succ expr2)) (simplify (times (const k) (succ (expr2))))))
simplify (times (succ (const k)) (succ (plus expr2 expr3))) = succ (simplePlus (const k) (simplePlus (simplify (plus expr2 expr3)) (simplify (times (const k) (plus expr2 expr3)))))
simplify (times (succ (const k)) (succ (times expr2 expr3))) = succ (simplePlus (const k) (simplePlus (simplify (times expr2 expr3)) (simplify (times (const k) (times expr2 expr3)))))
simplify (times (succ (const k)) (plus expr2 expr3)) = simplePlus (simplify (plus expr2 expr3)) (simplify (times (const k) (plus expr2 expr3)))
simplify (times (succ (const k)) (times expr2 expr3)) = simplePlus (simplify (times expr2 expr3)) (simplify (times (const k) (times expr2 expr3)))
simplify (times (succ (times expr1 expr3)) (const x)) = times (const x) (simplify (succ (times expr1 expr3)))
simplify (times (succ (times expr1 expr3)) zero) = zero
simplify (times (succ (times expr1 expr3)) (succ expr2)) = succ (simplePlus (simplify expr2) (plus (simplify (times expr1 expr3)) (simplify (times (times expr1 expr3) expr2))))
simplify (times (succ (times expr1 expr3)) (plus expr2 expr4)) = simplePlus (simplify (plus expr2 expr4)) (simplify (times (times expr1 expr3) (plus expr2 expr4)))
simplify (times (succ (times expr1 expr3)) (times expr2 expr4)) = simplePlus (simplify (times expr2 expr4)) (simplify (times (times expr1 expr3) (times expr2 expr4)))
simplify (times (plus expr1 expr3) zero) = zero
simplify (times (plus expr1 expr3) (succ expr2)) = simplePlus (simplify (plus expr1 expr3)) (simplify (times (plus expr1 expr3) expr2))
simplify (times (plus expr1 expr3) (const x)) = times (const x) (simplify (plus expr1 expr3))
simplify (times (plus expr1 expr3) (plus expr2 expr4)) = simplePlus (simplify (times expr1 expr2)) (simplePlus (simplify (times expr3 expr2)) (simplePlus (simplify (times expr1 expr4)) (simplify (times expr3 expr4))))
simplify (times (plus expr1 expr3) (times expr2 expr4)) = simplePlus (simplify (times expr1 (times expr2 expr4))) (simplify (times expr3 (times expr2 expr4)))
simplify (times (times expr1 expr3) zero) = zero
simplify (times (times expr1 expr3) (succ expr2)) = simplePlus (simplify (times expr1 expr3)) (simplify (times (times expr1 expr3) expr2))
simplify (times (times expr1 expr3) (plus expr2 expr4)) = simplePlus (simplify (times (times expr1 expr3) expr2)) (simplify (times (times expr1 expr3) expr4))
simplify (times (times expr1 expr3) (times expr2 expr4)) = times (simplify expr1) (simplify (times expr3 (times expr2 expr4)))
simplify (times (times expr1 expr3) (const x)) = times (simplify (times expr1 expr3)) (const x)

equalPlus : {a b c d : A} → (a ≡ c) → (b ≡ d) → (a + b) ≡ (c + d)
equalPlus refl refl = refl

equalTimes : {a b c d : A} → (a ≡ c) → (b ≡ d) → (a * b) ≡ (c * d)
equalTimes refl refl = refl

otherDist : {a b c : A} → (a * b) + (c * b) ≡ (a + c) * b
otherDist = transitivity (equalPlus (comm _ _) (comm _ _)) (transitivity (equalityCommutative (+DistributesOver* _ _ _)) (comm _ _))

simplifyPreserves : (a : Expr) → eval (simplify a) ≡ eval a
simplifyPreserves (const x) = refl
simplifyPreserves zero = refl
simplifyPreserves (succ a) = applyEquality (One +_) (simplifyPreserves a)
simplifyPreserves (plus (const x) (const y)) = refl
simplifyPreserves (plus (const x) zero) = equalityCommutative (sumZeroRight x)
simplifyPreserves (plus (const x) (succ b)) = transitivity (transitivity (applyEquality (One +_) (transitivity (simplifyPreserves (plus (const x) b)) (commutative x (eval b)))) (+Associative One (eval b) x)) (commutative (One + eval b) x)
simplifyPreserves (plus (const x) (plus b c)) = transitivity (simplePlusIsPlus (const x) (simplify (plus b c))) (applyEquality (x +_) (simplifyPreserves (plus b c)))
simplifyPreserves (plus (const x) (times b c)) = transitivity (simplePlusIsPlus (const x) (simplify (times b c))) (applyEquality (x +_) (simplifyPreserves (times b c)))
simplifyPreserves (plus zero a) = transitivity (simplifyPreserves a) (equalityCommutative (sumZeroLeft (eval a)))
simplifyPreserves (plus (succ a) b) = transitivity (applyEquality (One +_) (simplifyPreserves (plus a b))) (+Associative One (eval a) (eval b))
simplifyPreserves (plus (plus a b) (const x)) = transitivity (simplePlusIsPlus (const x) (simplify (plus a b))) (transitivity (commutative x (eval (simplify (plus a b)))) (applyEquality (_+ x) (simplifyPreserves (plus a b))))
simplifyPreserves (plus (plus a b) zero) = transitivity (simplifyPreserves (plus a b)) (equalityCommutative (sumZeroRight _))
simplifyPreserves (plus (plus a b) (succ c)) = transitivity (applyEquality (One +_) (simplePlusIsPlus (simplify (plus a b)) (simplify c))) (transitivity (+Associative One _ _) (transitivity (applyEquality (_+ eval (simplify c)) (commutative One _)) (transitivity (equalityCommutative (+Associative _ _ _)) (transitivity (applyEquality (_+ (One + eval (simplify c))) (simplifyPreserves (plus a b))) (applyEquality (λ i → (eval a + eval b) + (One + i)) (simplifyPreserves c))))))
simplifyPreserves (plus (plus a b) (plus c d)) = transitivity (simplePlusIsPlus (simplify (plus a b)) (simplify (plus c d))) (transitivity (applyEquality (_+ eval (simplify (plus c d))) (simplifyPreserves (plus a b))) (applyEquality ((eval a + eval b) +_) (simplifyPreserves (plus c d))))
simplifyPreserves (plus (plus a b) (times c d)) = transitivity (simplePlusIsPlus (simplify (plus a b)) (simplify (times c d))) (transitivity (applyEquality (_+ eval (simplify (times c d))) (simplifyPreserves (plus a b))) (applyEquality ((eval a + eval b) +_) (simplifyPreserves (times c d))))
simplifyPreserves (plus (times a b) (const x)) = transitivity (simplePlusIsPlus (const x) (simplify (times a b))) (transitivity (commutative x _) (applyEquality (_+ x) (simplifyPreserves (times a b))))
simplifyPreserves (plus (times a b) zero) = transitivity (transitivity (applyEquality (_* eval (simplify b)) (simplifyPreserves a)) (applyEquality ((eval a) *_) (simplifyPreserves b))) (equalityCommutative (sumZeroRight _))
simplifyPreserves (plus (times a b) (succ c)) = transitivity (transitivity (applyEquality (One +_) (transitivity (simplePlusIsPlus (simplify (times a b)) (simplify c)) (transitivity (transitivity (applyEquality (eval (simplify (times a b)) +_) (simplifyPreserves c)) (applyEquality (_+ eval c) (simplifyPreserves (times a b)))) (commutative _ (eval c))))) (+Associative One (eval c) _)) (commutative _ (eval a * eval b))
simplifyPreserves (plus (times a b) (plus c d)) = transitivity (simplePlusIsPlus (simplify (times a b)) (simplify (plus c d))) (transitivity (applyEquality (_+ eval (simplify (plus c d))) (simplifyPreserves (times a b))) (applyEquality ((eval a * eval b) +_) (simplifyPreserves (plus c d))))
simplifyPreserves (plus (times a b) (times c d)) = transitivity (simplePlusIsPlus (simplify (times a b)) (simplify (times c d))) (transitivity (applyEquality (_+ eval (simplify (times c d))) (simplifyPreserves (times a b))) (applyEquality ((eval a * eval b) +_) (simplifyPreserves (times c d))))
simplifyPreserves (times (const x) (const y)) = refl
simplifyPreserves (times (const x) zero) = equalityCommutative (productZeroRight x)
simplifyPreserves (times (const x) (succ (const y))) = transitivity (applyEquality (_+ (x * y)) (equalityCommutative (productOneRight _))) (equalityCommutative (+DistributesOver* x One y))
simplifyPreserves (times (const x) (succ zero)) = equalityCommutative (transitivity (applyEquality (x *_) (sumZeroRight One)) (productOneRight x))
simplifyPreserves (times (const x) (succ (succ b))) = transitivity (simplePlusIsPlus (const x) (simplify (times (const x) (succ b)))) (transitivity (equalPlus (equalityCommutative (productOneRight _)) (simplifyPreserves (times (const x) (succ b)))) (equalityCommutative (+DistributesOver* x One _)))
simplifyPreserves (times (const x) (succ (plus b c))) = transitivity (simplePlusIsPlus (const x) (simplePlus (simplify (times (const x) b)) (simplify (times (const x) c)))) (transitivity (equalPlus (equalityCommutative (productOneRight _)) (transitivity (simplePlusIsPlus (simplify (times (const x) b)) (simplify (times (const x) c))) (transitivity (equalPlus (simplifyPreserves (times (const x) b)) (simplifyPreserves (times (const x) c))) (equalityCommutative (+DistributesOver* x (eval b) (eval c)))))) (equalityCommutative (+DistributesOver* x One _)))
simplifyPreserves (times (const x) (succ (times b c))) = transitivity (equalPlus (equalityCommutative (productOneRight x)) (applyEquality (x *_) (simplifyPreserves (times b c)))) (equalityCommutative (+DistributesOver* x One _))
simplifyPreserves (times (const x) (plus b c)) = transitivity (simplePlusIsPlus (simplify (times (const x) b)) (simplify (times (const x) c))) (transitivity (transitivity (applyEquality (eval (simplify (times (const x) b)) +_) (simplifyPreserves (times (const x) c))) (applyEquality (_+ (x * eval c)) (simplifyPreserves (times (const x) b)))) (equalityCommutative (+DistributesOver* x (eval b) (eval c))))
simplifyPreserves (times (const x) (times b c)) = applyEquality (x *_) (simplifyPreserves (times b c))
simplifyPreserves (times zero b) = equalityCommutative (productZeroLeft (eval b))
simplifyPreserves (times (succ (const x)) (const y)) = transitivity (transitivity (equalPlus (equalityCommutative (productOneRight y)) (comm x y)) (equalityCommutative (+DistributesOver* y One x))) (comm y _)
simplifyPreserves (times (succ (const x)) zero) = equalityCommutative (productZeroRight _)
simplifyPreserves (times (succ (const x)) (succ (const y))) = transitivity (transitivity (transitivity (+Associative One x _) (applyEquality ((One + x) +_) (transitivity (equalPlus (equalityCommutative (productOneRight y)) (comm x y)) (equalityCommutative (+DistributesOver* y One x))))) (equalPlus (equalityCommutative (productOneRight (One + x))) (comm _ _))) (equalityCommutative (+DistributesOver* _ _ _))
simplifyPreserves (times (succ (const x)) (succ zero)) = equalityCommutative (transitivity (applyEquality ((One + x) *_) (sumZeroRight One)) (productOneRight _))
simplifyPreserves (times (succ (const x)) (succ (succ b))) = transitivity (applyEquality (One +_) (simplePlusIsPlus (const x) (simplePlus (succ (simplify b)) (simplify (times (const x) (succ b)))))) (transitivity (applyEquality (λ i → One + (x + i)) (simplePlusIsPlus (succ (simplify b)) (simplify (times (const x) (succ b))))) (transitivity (applyEquality (λ i → One + (x + ((One + i) + eval (simplify (times (const x) (succ b)))))) (simplifyPreserves b)) (transitivity (applyEquality (λ i → One + (x + ((One + eval b) + i))) (simplifyPreserves (times (const x) (succ b)))) (transitivity (transitivity (+Associative One x _) (equalPlus (equalityCommutative (productOneRight _)) (transitivity (transitivity (transitivity (applyEquality ((One + eval b) +_) (+DistributesOver* x One (eval b))) (transitivity (transitivity (equalityCommutative (+Associative One (eval b) _)) (transitivity (applyEquality (One +_) (transitivity (+Associative (eval b) _ _) (transitivity (equalPlus (transitivity (commutative _ _) (equalPlus (productOneRight x) (equalityCommutative (productOneRight _)))) (comm x _)) (equalityCommutative (+Associative x _ _))))) (+Associative One x _))) (applyEquality ((One + x) +_) (equalityCommutative (+DistributesOver* (eval b) One x))))) (equalPlus (equalityCommutative (productOneRight _)) (comm (eval b) _))) (equalityCommutative (+DistributesOver* (One + x) One _))))) (equalityCommutative (+DistributesOver* (One + x) One _))))))
simplifyPreserves (times (succ (const x)) (succ (plus b c))) = transitivity (transitivity (transitivity (applyEquality (One +_) (simplePlusIsPlus (const x) (simplePlus (simplify (plus b c)) (simplePlus (simplify (times (const x) b)) (simplify (times (const x) c)))))) (transitivity (+Associative One x _) (applyEquality ((One + x) +_) (transitivity (simplePlusIsPlus (simplify (plus b c)) (simplePlus (simplify (times (const x) b)) (simplify (times (const x) c)))) (transitivity (equalPlus (simplifyPreserves (plus b c)) (simplePlusIsPlus (simplify (times (const x) b)) (simplify (times (const x) c)))) (transitivity (transitivity (transitivity (transitivity (equalityCommutative (+Associative _ _ _ )) (transitivity (applyEquality (eval b +_) (transitivity (applyEquality (eval c +_) (equalPlus (simplifyPreserves (times (const x) b)) (simplifyPreserves (times (const x) c)))) (transitivity (+Associative (eval c) _ _) (transitivity (applyEquality (_+ (x * eval c)) (commutative _ _)) (equalityCommutative (+Associative _ _ _)))))) (+Associative _ _ _))) (equalPlus (equalPlus (equalityCommutative (productOneRight (eval b))) (comm _ _)) (equalPlus (equalityCommutative (productOneRight (eval c))) (comm x _)))) (equalPlus (equalityCommutative (+DistributesOver* (eval b) One x)) (equalityCommutative (+DistributesOver* (eval c) One x)))) (equalPlus (comm _ _) (comm _ _)))))))) (equalPlus (equalityCommutative (productOneRight _)) (equalityCommutative (+DistributesOver* (One + x) _ _)))) (equalityCommutative (+DistributesOver* (One + x) _ _))
simplifyPreserves (times (succ (const x)) (succ (times b c))) = transitivity (transitivity (applyEquality (One +_) (simplePlusIsPlus (const x) (simplePlus (simplify (times b c)) (times (const x) (simplify (times b c)))))) (transitivity (+Associative One x _) (equalPlus (equalityCommutative (productOneRight _)) (transitivity (simplePlusIsPlus (simplify (times b c)) (times (const x) (simplify (times b c)))) (transitivity (transitivity (equalPlus (transitivity (simplifyPreserves (times b c)) (equalityCommutative (productOneRight _))) (transitivity (comm _ _) (applyEquality (_* x) (simplifyPreserves (times b c))))) (equalityCommutative (+DistributesOver* _ One x))) (comm _ _)))))) (equalityCommutative (+DistributesOver* _ _ _))
simplifyPreserves (times (succ (const x)) (plus b c)) = transitivity (simplePlusIsPlus (simplify (plus b c)) (simplePlus (simplify (times (const x) b)) (simplify (times (const x) c)))) (transitivity (transitivity (equalPlus (transitivity (simplifyPreserves (plus b c)) (equalityCommutative (productOneRight _))) (transitivity (simplePlusIsPlus (simplify (times (const x) b)) (simplify (times (const x) c))) (transitivity (transitivity (equalPlus (simplifyPreserves (times (const x) b)) (simplifyPreserves (times (const x) c))) (equalityCommutative (+DistributesOver* x _ _))) (comm x _)))) (equalityCommutative (+DistributesOver* _ One x))) (comm _ _))
simplifyPreserves (times (succ (const x)) (times b c)) = transitivity (simplePlusIsPlus (simplify (times b c)) (times (const x) (simplify (times b c)))) (transitivity (transitivity (equalPlus (transitivity (simplifyPreserves (times b c)) (equalityCommutative (productOneRight _))) (transitivity (comm x _) (applyEquality (_* x) (simplifyPreserves (times b c))))) (equalityCommutative (+DistributesOver* _ One x))) (comm _ _))
simplifyPreserves (times (succ zero) b) = transitivity (simplifyPreserves b) (transitivity (equalityCommutative (productOneLeft (eval b))) (applyEquality (_* eval b) (equalityCommutative (sumZeroRight One))))
simplifyPreserves (times (succ (succ a)) b) = transitivity (simplePlusIsPlus (simplify b) (simplify (times (succ a) b))) (transitivity (equalPlus (simplifyPreserves b) (simplifyPreserves (times (succ a) b))) (transitivity (transitivity (equalPlus (equalityCommutative (productOneRight _)) (comm _ _)) (equalityCommutative (+DistributesOver* (eval b) One _))) (comm (eval b) _)))
simplifyPreserves (times (succ (plus a b)) (const x)) = transitivity (comm x _) (applyEquality (λ i → (One + i) * x) (simplifyPreserves (plus a b)))
simplifyPreserves (times (succ (plus a b)) zero) = equalityCommutative (productZeroRight _)
simplifyPreserves (times (succ (plus a b)) (succ c)) = transitivity (transitivity (transitivity (applyEquality (One +_) (transitivity (simplePlusIsPlus (simplify (times a c)) (simplePlus (simplify (times b c)) (simplePlus c (simplify (plus a b))))) (transitivity (transitivity (equalPlus (simplifyPreserves (times a c)) (simplePlusIsPlus (simplify (times b c)) (simplePlus c (simplify (plus a b))))) (transitivity (+Associative _ _ _) (transitivity (transitivity (equalPlus (transitivity (equalPlus (comm _ _) (transitivity (simplifyPreserves (times b c)) (comm _ _))) (equalityCommutative (+DistributesOver* _ _ _))) (transitivity (simplePlusIsPlus c (simplify (plus a b))) (transitivity (commutative _ _) (equalPlus (simplifyPreserves (plus a b)) (equalityCommutative (productOneRight _)))))) (commutative _ _)) (equalityCommutative (+Associative _ _ _))))) (applyEquality ((eval a + eval b) +_) (equalityCommutative (+DistributesOver* _ One _)))))) (+Associative One _ _)) (equalPlus (equalityCommutative (productOneRight _)) (comm _ _))) (equalityCommutative (+DistributesOver* _ _ _))
simplifyPreserves (times (succ (plus a b)) (plus c d)) = equalTimes (applyEquality (One +_) (simplifyPreserves (plus a b))) (simplifyPreserves (plus c d))
simplifyPreserves (times (succ (plus a b)) (times c d)) = equalTimes (applyEquality (One +_) (simplifyPreserves (plus a b))) (simplifyPreserves (times c d))
simplifyPreserves (times (succ (times a b)) (const x)) = transitivity (comm x _) (applyEquality (λ i → (One + i) * x) (simplifyPreserves (times a b)))
simplifyPreserves (times (succ (times a b)) zero) = equalityCommutative (productZeroRight _)
simplifyPreserves (times (succ (times a b)) (succ c)) = transitivity (transitivity (transitivity (applyEquality (One +_) (transitivity (simplePlusIsPlus (simplify c) (plus (simplify (times a b)) (simplify (times (times a b) c)))) (transitivity (transitivity (transitivity (equalPlus (transitivity (simplifyPreserves c) (equalityCommutative (productOneRight _))) (transitivity (commutative _ _) (equalPlus (transitivity (simplifyPreserves (times (times a b) c)) (comm _ _)) (simplifyPreserves (times a b))))) (+Associative _ _ _)) (applyEquality (_+ (eval a * eval b)) (equalityCommutative (+DistributesOver* _ One _)))) (commutative _ _)))) (+Associative One _ _)) (equalPlus (equalityCommutative (productOneRight _)) (comm _ _))) (equalityCommutative (+DistributesOver* _ One _))
simplifyPreserves (times (succ (times a b)) (plus c d)) = transitivity (simplePlusIsPlus (simplify (plus c d)) (simplePlus (simplify (times (times a b) c)) (simplify (times (times a b) d)))) (transitivity (equalPlus (simplifyPreserves (plus c d)) (simplePlusIsPlus (simplify (times (times a b) c)) (simplify (times (times a b) d)))) (transitivity (transitivity (equalPlus (equalityCommutative (productOneRight _)) (transitivity (transitivity (equalPlus (simplifyPreserves (times (times a b) c)) (simplifyPreserves (times (times a b) d))) (equalityCommutative (+DistributesOver* _ _ _))) (comm _ _))) (equalityCommutative (+DistributesOver* _ One _))) (comm _ _)))
simplifyPreserves (times (succ (times a b)) (times c d)) = transitivity (simplePlusIsPlus (simplify (times c d)) (times (simplify a) (simplify (times b (times c d))))) (transitivity (equalPlus (simplifyPreserves (times c d)) (equalTimes (simplifyPreserves a) (simplifyPreserves (times b (times c d))))) (transitivity (transitivity (equalPlus (equalityCommutative (productOneRight _)) (transitivity (*Associative (eval a) _ _) (comm _ _))) (equalityCommutative (+DistributesOver* _ One _))) (comm _ _)))
simplifyPreserves (times (plus a b) (const x)) = transitivity (comm x _) (applyEquality (_* x) (simplifyPreserves (plus a b)))
simplifyPreserves (times (plus a b) zero) = equalityCommutative (productZeroRight _)
simplifyPreserves (times (plus a b) (succ c)) = transitivity (simplePlusIsPlus (simplify (plus a b)) (simplify (times (plus a b) c))) (transitivity (applyEquality ((eval (simplify (plus a b))) +_) (simplifyPreserves (times (plus a b) c))) (transitivity (applyEquality (_+ ((eval a + eval b) * eval c)) (simplifyPreserves (plus a b))) (transitivity (equalPlus (equalityCommutative (productOneRight _)) refl) (equalityCommutative (+DistributesOver* _ One (eval c))))))
simplifyPreserves (times (plus a b) (plus c d)) = transitivity (simplePlusIsPlus (simplify (times a c)) (simplePlus (simplify (times b c)) (simplePlus (simplify (times a d)) (simplify (times b d))))) (transitivity (transitivity (transitivity (transitivity (equalPlus (transitivity (simplifyPreserves (times a c)) (comm _ _)) (transitivity (simplePlusIsPlus (simplify (times b c)) (simplePlus (simplify (times a d)) (simplify (times b d)))) (equalPlus (transitivity (simplifyPreserves (times b c)) (comm _ _)) (transitivity (simplePlusIsPlus (simplify (times a d)) (simplify (times b d))) (equalPlus (transitivity (simplifyPreserves (times a d)) (comm _ _)) (transitivity (simplifyPreserves (times b d)) (comm _ _))))))) (+Associative _ _ _)) (equalPlus (equalityCommutative (+DistributesOver* (eval c) (eval a) _)) (equalityCommutative (+DistributesOver* (eval d) (eval a) _)))) (equalPlus (comm (eval c) _) (comm (eval d) _))) (equalityCommutative (+DistributesOver* _ (eval c) (eval d))))
simplifyPreserves (times (plus a b) (times c d)) = transitivity (simplePlusIsPlus (simplify (times a (times c d))) (simplify (times b (times c d)))) (transitivity (equalPlus (simplifyPreserves (times a (times c d))) (simplifyPreserves (times b (times c d)))) (transitivity (equalPlus (comm (eval a) _) (comm (eval b) _)) (transitivity (equalityCommutative (+DistributesOver* _ (eval a) (eval b))) (comm _ _))))
simplifyPreserves (times (times a b) (const x)) = applyEquality (_* x) (simplifyPreserves (times a b))
simplifyPreserves (times (times a b) zero) = equalityCommutative (productZeroRight _)
simplifyPreserves (times (times a b) (succ c)) = transitivity (simplePlusIsPlus (simplify (times a b)) (simplify (times (times a b) c))) (transitivity (equalPlus (simplifyPreserves (times a b)) (simplifyPreserves (times (times a b) c))) (transitivity (applyEquality (_+ ((eval a * eval b) * eval c)) (equalityCommutative (productOneRight _))) (equalityCommutative (+DistributesOver* _ One (eval c)))))
simplifyPreserves (times (times a b) (plus c d)) = transitivity (simplePlusIsPlus (simplify (times (times a b) c)) (simplify (times (times a b) d))) (transitivity (equalPlus (simplifyPreserves (times (times a b) c)) (simplifyPreserves (times (times a b) d))) (equalityCommutative (+DistributesOver* _ _ _)))
simplifyPreserves (times (times a b) (times c d)) = transitivity (equalTimes (simplifyPreserves a) (simplifyPreserves (times b (times c d)))) (*Associative (eval a) (eval b) _)

from_to_by_ : (x y : Expr) (pr : eval (simplify x) ≡ eval (simplify y)) → eval x ≡ eval y
from a to b by pr = transitivity (equalityCommutative (simplifyPreserves a)) (transitivity pr (simplifyPreserves b))
