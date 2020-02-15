{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring -- for length
open import Numbers.Naturals.Order
open import Semirings.Definition
open import Maybe

module Lists.Lists where

open import Lists.Definition public
open import Lists.Length public
open import Lists.Concat public
open import Lists.Map.Map public
open import Lists.Reversal.Reversal public
open import Lists.Monad public
open import Lists.Filter.AllTrue public
open import Lists.Fold.Fold public

replicate : {a : _} {A : Set a} (n : ℕ) (x : A) → List A
replicate zero x = []
replicate (succ n) x = x :: replicate n x

head : {a : _} {A : Set a} (l : List A) (pr : 0 <N length l) → A
head [] (le x ())
head (x :: l) pr = x

lengthRev : {a : _} {A : Set a} (l : List A) → length (rev l) ≡ length l
lengthRev [] = refl
lengthRev (x :: l) rewrite lengthConcat (rev l) (x :: []) | lengthRev l | Semiring.commutative ℕSemiring (length l) 1 = refl

listLast : {a : _} {A : Set a} (l : List A) → Maybe A
listLast [] = no
listLast (x :: []) = yes x
listLast (x :: y :: l) = listLast (y :: l)

listZip : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) → (f1 : A → C) → (f2 : B → C) →(l1 : List A) (l2 : List B) → List C
listZip f f1 f2 [] l2 = map f2 l2
listZip f f1 f2 (x :: l1) [] = map f1 (x :: l1)
listZip f f1 f2 (x :: l1) (y :: l2) = (f x y) :: listZip f f1 f2 l1 l2

contains : {a : _} {A : Set a} (l : List A) (needle : A) → Set a
contains [] needle = False'
contains (x :: l) needle = (x ≡ needle) || contains l needle

containsMap : {a b : _} {A : Set a} {B : Set b} (f : A → B) (l : List A) (needle : A) → (contains l needle) → contains (map f l) (f needle)
containsMap f (x :: l) needle (inl cont) = inl (applyEquality f cont)
containsMap f (x :: l) needle (inr cont) = inr (containsMap f l needle cont)
