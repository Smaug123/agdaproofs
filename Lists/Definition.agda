{-# OPTIONS --safe --warning=error --without-K #-}


module Lists.Definition where

data List {a : _} (A : Set a) : Set a where
  [] : List A
  _::_ : (x : A) (xs : List A) → List A
infixr 10 _::_
{-# BUILTIN LIST List #-}

[_] : {a : _} {A : Set a} → (a : A) → List A
[ a ] = a :: []

_++_ : {a : _} {A : Set a} → List A → List A → List A
[] ++ m = m
(x :: l) ++ m = x :: (l ++ m)
