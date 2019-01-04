{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Naturals -- for length

module Lists where
  data Vec {a} (A : Set a) : ℕ → Set a where
    [] : Vec A 0
    _::_ : {len : ℕ} (x : A) (xs : Vec A len) → Vec A (succ len)

  [_] : {a : _} → {A : Set a} → (a : A) → Vec A 1
  [ a ] = a :: []

  _++_ : {a : _} → {A : Set a} → {m n : ℕ} → Vec A m → Vec A n → Vec A (m +N n)
  [] ++ m = m
  (x :: l) ++ m = x :: (l ++ m)

  appendEmptyList : {a : _} → {A : Set a} → {m : ℕ} → (l : Vec A m) → (l ++ [] ≡ l)
  appendEmptyList [] = refl
  appendEmptyList (x :: l) = applyEquality (_::_ x) (appendEmptyList l)

  concatAssoc : {a : _} → {A : Set a} → {m n o : ℕ} → (x : Vec A m) → (y : Vec A n) → (z : Vec A o) → ((x ++ y) ++ z) ≡ x ++ (y ++ z)
  concatAssoc [] m n = refl
  concatAssoc (x :: l) m n = applyEquality (_::_ x) (concatAssoc l m n)

  canMovePrepend : {a : _} → {A : Set a} → (l : A) → {m n : ℕ} → (x : Vec A m) (y : Vec A n) → ((l :: x) ++ y ≡ l :: (x ++ y))
  canMovePrepend l [] n = refl
  canMovePrepend l (x :: m) n = refl

  rev : {a : _} → {A : Set a} → {m : ℕ} → Vec A m → Vec A m
  rev [] = []
  rev (x :: l) = (rev l) ++ [ x ]

  revIsHom : {a : _} → {A : Set a} → {m n : ℕ} → (l1 : Vec A m) → (l2 : Vec A n) → (rev (l1 ++ l2) ≡ (rev l2) ++ (rev l1))
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

  revRevIsId : {a : _} → {A : Set a} → {m : ℕ} → (l : Vec A m) → (rev (rev l) ≡ l)
  revRevIsId [] = refl
  revRevIsId (x :: l) = t
    where
      s : rev (rev l ++ [ x ] ) ≡ [ x ] ++ rev (rev l)
      s = revIsHom (rev l) [ x ]
      t : rev (rev l ++ [ x ] ) ≡ [ x ] ++ l
      t = identityOfIndiscernablesRight (rev (rev l ++ (x :: []))) ([ x ] ++ rev (rev l)) ([ x ] ++ l) _≡_ s (applyEquality (λ n → [ x ] ++ n) (revRevIsId l))

  map : {a : _} → {b : _} → {A : Set a} → {B : Set b} → {m : ℕ} → (f : A → B) → Vec A m → Vec B m
  map f [] = []
  map f (x :: list) = (f x) :: (map f list)
