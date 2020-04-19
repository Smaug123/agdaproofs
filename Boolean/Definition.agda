{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Boolean.Definition where

data Bool : Set where
  BoolTrue : Bool
  BoolFalse : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  BoolTrue  #-}
{-# BUILTIN FALSE BoolFalse #-}

if_then_else_ : {a : _} → {A : Set a} → Bool → A → A → A
if BoolTrue then tr else fls = tr
if BoolFalse then tr else fls = fls

not : Bool → Bool
not BoolTrue = BoolFalse
not BoolFalse = BoolTrue

boolAnd : Bool → Bool → Bool
boolAnd BoolTrue y = y
boolAnd BoolFalse y = BoolFalse

boolOr : Bool → Bool → Bool
boolOr BoolTrue y = BoolTrue
boolOr BoolFalse y = y

xor : Bool → Bool → Bool
xor BoolTrue BoolTrue = BoolFalse
xor BoolTrue BoolFalse = BoolTrue
xor BoolFalse b = b
