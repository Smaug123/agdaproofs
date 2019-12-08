{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Semiring -- for length
open import Numbers.Naturals.Order
open import Semirings.Definition
open import Maybe
open import Lists.Definition
open import Lists.Concat

module Lists.Reversal.Reversal where

rev : {a : _} → {A : Set a} → List A → List A
rev [] = []
rev (x :: l) = (rev l) ++ [ x ]

revIsHom : {a : _} → {A : Set a} → (l1 : List A) → (l2 : List A) → (rev (l1 ++ l2) ≡ (rev l2) ++ (rev l1))
revIsHom l1 [] = applyEquality rev (appendEmptyList l1)
revIsHom [] (x :: l2) with (rev l2 ++ [ x ])
... | r = equalityCommutative (appendEmptyList r)
revIsHom (w :: l1) (x :: l2) = transitivity t (equalityCommutative s)
  where
    s : ((rev l2 ++ [ x ]) ++ (rev l1 ++ [ w ])) ≡ (((rev l2 ++ [ x ]) ++ rev l1) ++ [ w ])
    s = equalityCommutative (concatAssoc (rev l2 ++ (x :: [])) (rev l1) ([ w ]))
    t' : rev (l1 ++ (x :: l2)) ≡ rev (x :: l2) ++ rev l1
    t' = revIsHom l1 (x :: l2)
    t : (rev (l1 ++ (x :: l2)) ++ [ w ]) ≡ ((rev l2 ++ [ x ]) ++ rev l1) ++ [ w ]
    t = applyEquality (λ r → r ++ [ w ]) {rev (l1 ++ (x :: l2))} {((rev l2) ++ [ x ]) ++ rev l1} (transitivity t' (applyEquality (λ r → r ++ rev l1) {rev l2 ++ (x :: [])} {rev l2 ++ (x :: [])} refl))

revRevIsId : {a : _} → {A : Set a} → (l : List A) → (rev (rev l) ≡ l)
revRevIsId [] = refl
revRevIsId (x :: l) = t
  where
    s : rev (rev l ++ [ x ] ) ≡ [ x ] ++ rev (rev l)
    s = revIsHom (rev l) [ x ]
    t : rev (rev l ++ [ x ] ) ≡ [ x ] ++ l
    t = identityOfIndiscernablesRight _≡_ s (applyEquality (λ n → [ x ] ++ n) (revRevIsId l))
