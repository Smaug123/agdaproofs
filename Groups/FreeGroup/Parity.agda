{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Groups.FreeGroup.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Decidable.Sets
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Semirings.Definition
open import Functions.Definition
open import Groups.Isomorphisms.Definition
open import Boolean.Definition
open import Boolean.Lemmas

module Groups.FreeGroup.Parity {a : _} {A : Set a} (decA : DecidableSet A) where

open import Groups.FreeGroup.Word decA
open import Groups.FreeGroup.Group decA

C2 : Group (reflSetoid Bool) xor
Group.+WellDefined C2 refl refl = refl
Group.0G C2 = BoolFalse
Group.inverse C2 = id
Group.+Associative C2 {BoolTrue} {BoolTrue} {BoolTrue} = refl
Group.+Associative C2 {BoolTrue} {BoolTrue} {BoolFalse} = refl
Group.+Associative C2 {BoolTrue} {BoolFalse} {z} = refl
Group.+Associative C2 {BoolFalse} {y} {z} = refl
Group.identRight C2 {BoolTrue} = refl
Group.identRight C2 {BoolFalse} = refl
Group.identLeft C2 {x} = refl
Group.invLeft C2 {BoolTrue} = refl
Group.invLeft C2 {BoolFalse} = refl
Group.invRight C2 {BoolTrue} = refl
Group.invRight C2 {BoolFalse} = refl

parity : (x : A) → ReducedWord → Bool
parity x empty = BoolFalse
parity x (prependLetter (ofLetter y) w _) with decA x y
parity x (prependLetter (ofLetter y) w _) | inl _ = not (parity x w)
parity x (prependLetter (ofLetter y) w _) | inr _ = parity x w
parity x (prependLetter (ofInv y) w _) with decA x y
parity x (prependLetter (ofInv y) w _) | inl _ = not (parity x w)
parity x (prependLetter (ofInv y) w _) | inr _ = parity x w

private
  parityPrepend : (a : A) (w : ReducedWord) (l : A) → ((a ≡ l) → False) → parity a (prepend w (ofLetter l)) ≡ parity a w
  parityPrepend a empty l notEq with decA a l
  parityPrepend a empty l notEq | inl x = exFalso (notEq x)
  parityPrepend a empty l notEq | inr x = refl
  parityPrepend a (prependLetter (ofLetter r) w x) l notEq with decA a l
  parityPrepend a (prependLetter (ofLetter r) w x) l notEq | inl m = exFalso (notEq m)
  parityPrepend a (prependLetter (ofLetter r) w x) l notEq | inr _ = refl
  parityPrepend a (prependLetter (ofInv r) w x) l notEq with decA a r
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inl a=r with decA l r
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inl a=r | inl l=r = exFalso (notEq (transitivity a=r (equalityCommutative l=r)))
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r with decA a l
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inl a=l = exFalso (notEq a=l)
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inr a!=l with decA a r
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inr a!=l | inl x₁ = refl
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inr a!=l | inr bad = exFalso (bad a=r)
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inr a!=r with decA l r
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inl x₁ = refl
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r with decA a l
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inl a=l = exFalso (notEq a=l)
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inr a!=l with decA a r
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inr a!=l | inl a=r = exFalso (a!=r a=r)
  parityPrepend a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inr a!=l | inr x₁ = refl

  parityPrepend' : (a : A) (w : ReducedWord) (l : A) → ((a ≡ l) → False) → parity a (prepend w (ofInv l)) ≡ parity a w
  parityPrepend' a empty l notEq with decA a l
  parityPrepend' a empty l notEq | inl x = exFalso (notEq x)
  parityPrepend' a empty l notEq | inr x = refl
  parityPrepend' a (prependLetter (ofLetter r) w x) l notEq with decA l r
  parityPrepend' a (prependLetter (ofLetter r) w x) l notEq | inl m with decA a r
  ... | inl a=r = exFalso (notEq (transitivity a=r (equalityCommutative m)))
  ... | inr a!=r = refl
  parityPrepend' a (prependLetter (ofLetter r) w x) l notEq | inr l!=r with decA a l
  ... | inl a=l = exFalso (notEq a=l)
  ... | inr a!=l = refl
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq with decA a r
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inl a=r with decA l r
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inl a=r | inl l=r = exFalso (notEq (transitivity a=r (equalityCommutative l=r)))
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r with decA a l
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inl a=l = exFalso (notEq a=l)
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inr a!=l with decA a r
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inr a!=l | inl x₁ = refl
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inl a=r | inr l!=r | inr a!=l | inr bad = exFalso (bad a=r)
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r with decA l r
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inl l=r with decA a l
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inl l=r | inl a=l = exFalso (notEq a=l)
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inl l=r | inr a!=l with decA a r
  ... | inl a=r = exFalso (a!=r a=r)
  ... | inr _ = refl
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r with decA a l
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inl a=l = exFalso (notEq a=l)
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inr a!=l with decA a r
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inr a!=l | inl a=r = exFalso (a!=r a=r)
  parityPrepend' a (prependLetter (ofInv r) w x) l notEq | inr a!=r | inr l!=r | inr a!=l | inr x₁ = refl

  parityPrepend'' : (a : A) (w : ReducedWord) → parity a (prepend w (ofLetter a)) ≡ not (parity a w)
  parityPrepend'' a empty with decA a a
  ... | inl _ = refl
  ... | inr bad = exFalso (bad refl)
  parityPrepend'' a (prependLetter (ofLetter l) w x) with decA a a
  parityPrepend'' a (prependLetter (ofLetter l) w x) | inl _ with decA a l
  parityPrepend'' a (prependLetter (ofLetter l) w x) | inl _ | inl a=l = refl
  parityPrepend'' a (prependLetter (ofLetter l) w x) | inl _ | inr a!=l = refl
  parityPrepend'' a (prependLetter (ofLetter l) w x) | inr bad = exFalso (bad refl)
  parityPrepend'' a (prependLetter (ofInv l) w x) with decA a l
  ... | inl a=l = equalityCommutative (notNot (parity a w))
  parityPrepend'' a (prependLetter (ofInv l) w x) | inr a!=l with decA a a
  parityPrepend'' a (prependLetter (ofInv l) w x) | inr a!=l | inl _ with decA a l
  ... | inl a=l = exFalso (a!=l a=l)
  ... | inr _ = refl
  parityPrepend'' a (prependLetter (ofInv l) w x) | inr a!=l | inr bad = exFalso (bad refl)

  parityPrepend''' : (a : A) (w : ReducedWord) → parity a (prepend w (ofInv a)) ≡ not (parity a w)
  parityPrepend''' a empty with decA a a
  ... | inl _ = refl
  ... | inr bad = exFalso (bad refl)
  parityPrepend''' a (prependLetter (ofLetter l) w x) with decA a l
  ... | inl a=l = equalityCommutative (notNot _)
  parityPrepend''' a (prependLetter (ofLetter l) w x) | inr a!=l with decA a a
  ... | inl _ with decA a l
  parityPrepend''' a (prependLetter (ofLetter l) w x) | inr a!=l | inl _ | inl a=l = exFalso (a!=l a=l)
  parityPrepend''' a (prependLetter (ofLetter l) w x) | inr a!=l | inl _ | inr _ = refl
  parityPrepend''' a (prependLetter (ofLetter l) w x) | inr a!=l | inr bad = exFalso (bad refl)
  parityPrepend''' a (prependLetter (ofInv l) w x) with decA a a
  parityPrepend''' a (prependLetter (ofInv l) w x) | inl _ with decA a l
  ... | inl a=l = refl
  ... | inr a!=l = refl
  parityPrepend''' a (prependLetter (ofInv l) w x) | inr bad = exFalso (bad refl)

  parityHomIsHom : (a : A) → (x y : ReducedWord) → parity a (_+W_ x y) ≡ xor (parity a x) (parity a y)
  parityHomIsHom a empty y = refl
  parityHomIsHom a (prependLetter (ofLetter l) x _) y with decA a l
  parityHomIsHom a (prependLetter (ofLetter .a) x _) y | inl refl = transitivity (parityPrepend'' a (x +W y)) (transitivity (applyEquality not (parityHomIsHom a x y)) (notXor (parity a x) (parity a y)))
  parityHomIsHom a (prependLetter (ofLetter l) x _) y | inr a!=l = transitivity (parityPrepend a (_+W_ x y) l a!=l) (parityHomIsHom a x y)
  parityHomIsHom a (prependLetter (ofInv l) x _) y with decA a l
  parityHomIsHom a (prependLetter (ofInv .a) x _) y | inl refl = transitivity (parityPrepend''' a (x +W y)) (transitivity (applyEquality not (parityHomIsHom a x y)) (notXor (parity a x) (parity a y)))
  parityHomIsHom a (prependLetter (ofInv l) x _) y | inr a!=l = transitivity (parityPrepend' a (x +W y) l a!=l) (parityHomIsHom a x y)

parityHom : (x : A) → GroupHom (freeGroup) C2 (parity x)
GroupHom.groupHom (parityHom x) {y} {z} = parityHomIsHom x y z
GroupHom.wellDefined (parityHom x) refl = refl
