{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals -- for length

module Lists where
  data List {a} (A : Set a) : Set a where
    [] : List A
    _::_ : (x : A) (l : List A) → List A

  [_] : {a : _} {A : Set a} (x : A) → List A
  [ a ] = a :: []

  listMap : {a b : _} {A : Set a} {B : Set b} (f : A → B) → (l : List A) → List B
  listMap f [] = []
  listMap f (x :: l) = (f x) :: listMap f l

  _++_ : {a : _} {A : Set a} (l1 l2 : List A) → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)

  listRev : {a : _} {A : Set a} (l : List A) → List A
  listRev [] = []
  listRev (x :: l) = (listRev l) ++ [ x ]

  appendEmptyList : {a : _} {A : Set a} (l : List A) → (l ++ []) ≡ l
  appendEmptyList [] = refl
  appendEmptyList (x :: l) = applyEquality (λ t → x :: t) (appendEmptyList l)
