{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Lists.Definition
open import Lists.Length
open import Numbers.Naturals.Semiring

module Lists.Concat where

appendEmptyList : {a : _} → {A : Set a} → (l : List A) → (l ++ [] ≡ l)
appendEmptyList [] = refl
appendEmptyList (x :: l) = applyEquality (_::_ x) (appendEmptyList l)

concatAssoc : {a : _} → {A : Set a} → (x : List A) → (y : List A) → (z : List A) → ((x ++ y) ++ z) ≡ x ++ (y ++ z)
concatAssoc [] m n = refl
concatAssoc (x :: l) m n = applyEquality (_::_ x) (concatAssoc l m n)

canMovePrepend : {a : _} → {A : Set a} → (l : A) → (x : List A) (y : List A) → ((l :: x) ++ y ≡ l :: (x ++ y))
canMovePrepend l [] n = refl
canMovePrepend l (x :: m) n = refl

lengthConcat : {a : _} {A : Set a} (l1 l2 : List A) → length (l1 ++ l2) ≡ length l1 +N length l2
lengthConcat [] l2 = refl
lengthConcat (x :: l1) l2 = applyEquality succ (lengthConcat l1 l2)
