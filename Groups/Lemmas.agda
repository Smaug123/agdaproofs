{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Groups.Definition
open import Sets.EquivalenceRelations

module Groups.Lemmas {a b : _} {A : Set a} {_·_ : A → A → A} {S : Setoid {a} {b} A} (G : Group S _·_) where

open Setoid S
open Group G
open Equivalence eq

groupsHaveLeftCancellation : (x y z : A) → (x · y) ∼ (x · z) → y ∼ z
groupsHaveLeftCancellation x y z pr = o
  where
  _^-1 = inverse
  j : ((x ^-1) · x) · y ∼ (x ^-1) · (x · z)
  j = transitive (symmetric (+Associative {x ^-1} {x} {y})) (+WellDefined ~refl pr)
  k : ((x ^-1) · x) · y ∼ ((x ^-1) · x) · z
  k = transitive j +Associative
  l : 0G · y ∼ ((x ^-1) · x) · z
  l = transitive (+WellDefined (symmetric invLeft) ~refl) k
  m : 0G · y ∼ 0G · z
  m = transitive l (+WellDefined invLeft ~refl)
  n : y ∼ 0G · z
  n = transitive (symmetric identLeft) m
  o : y ∼ z
  o = transitive n identLeft

groupsHaveRightCancellation : (x y z : A) → (y · x) ∼ (z · x) → y ∼ z
groupsHaveRightCancellation x y z pr = transitive m identRight
  where
  _^-1 = inverse
  i : (y · x) · (x ^-1) ∼ (z · x) · (x ^-1)
  i = +WellDefined pr ~refl
  j : y · (x · (x ^-1)) ∼ (z · x) · (x ^-1)
  j = transitive +Associative i
  j' : y · 0G ∼ (z · x) · (x ^-1)
  j' = transitive (+WellDefined ~refl (symmetric invRight)) j
  k : y ∼ (z · x) · (x ^-1)
  k = transitive (symmetric identRight) j'
  l : y ∼ z · (x · (x ^-1))
  l = transitive k (symmetric +Associative)
  m : y ∼ z · 0G
  m = transitive l (+WellDefined ~refl invRight)

rightInversesAreUnique : (x : A) → (y : A) → (y · x) ∼ 0G → y ∼ (inverse x)
rightInversesAreUnique x y f = transitive i (transitive j (transitive k (transitive l m)))
  where
  _^-1 = inverse
  i : y ∼ y · 0G
  j : y · 0G ∼ y · (x · (x ^-1))
  k : y · (x · (x ^-1)) ∼ (y · x) · (x ^-1)
  l : (y · x) · (x ^-1) ∼ 0G · (x ^-1)
  m : 0G · (x ^-1) ∼ x ^-1
  i = symmetric identRight
  j = +WellDefined ~refl (symmetric invRight)
  k = +Associative
  l = +WellDefined f ~refl
  m = identLeft

leftInversesAreUnique : {x : A} → {y : A} → (x · y) ∼ 0G → y ∼ (inverse x)
leftInversesAreUnique {x} {y} f = rightInversesAreUnique x y l
  where
    _^-1 = inverse
    i : y · (x · y) ∼ y · 0G
    i' : y · (x · y) ∼ y
    j : (y · x) · y ∼ y
    k : (y · x) · y ∼ 0G · y
    l : y · x ∼ 0G
    i = +WellDefined ~refl f
    i' = transitive i identRight
    j = transitive (symmetric +Associative) i'
    k = transitive j (symmetric identLeft)
    l = groupsHaveRightCancellation y (y · x) 0G k


invTwice : (x : A) → (inverse (inverse x)) ∼ x
invTwice x = symmetric (rightInversesAreUnique (x ^-1) x invRight)
  where
  _^-1 = inverse

replaceGroupOp : {a b c d w x y z : A} → (Setoid._∼_ S a c) → (Setoid._∼_ S b d) → (Setoid._∼_ S w y) → (Setoid._∼_ S x z) → Setoid._∼_ S (a · b) (w · x) → Setoid._∼_ S (c · d) (y · z)
replaceGroupOp a~c b~d w~y x~z pr = transitive (symmetric (+WellDefined a~c b~d)) (transitive pr (+WellDefined w~y x~z))

replaceGroupOpRight : {a b c x : A} → (Setoid._∼_ S a (b · c)) → (Setoid._∼_ S c x) → (Setoid._∼_ S a (b · x))
replaceGroupOpRight a~bc c~x = transitive a~bc (+WellDefined reflexive c~x)

inverseWellDefined : {x y : A} → (x ∼ y) → (inverse x) ∼ (inverse y)
inverseWellDefined {x} {y} x~y = groupsHaveRightCancellation x (inverse x) (inverse y) q
  where
    p : inverse x · x ∼ inverse y · y
    p = transitive invLeft (symmetric invLeft)
    q : inverse x · x ∼ inverse y · x
    q = replaceGroupOpRight {_·_ (inverse x) x} {inverse y} {y} {x} p (symmetric x~y)

transferToRight : {a b : A} → (a · (inverse b)) ∼ 0G → a ∼ b
transferToRight {a} {b} ab-1 = transitive (symmetric (invTwice a)) (transitive u (invTwice b))
  where
    t : inverse a ∼ inverse b
    t = symmetric (leftInversesAreUnique ab-1)
    u : inverse (inverse a) ∼ inverse (inverse b)
    u = inverseWellDefined t

transferToRight' : {a b : A} → (a · b) ∼ 0G → a ∼ (inverse b)
transferToRight' {a} {b} ab-1 = transferToRight lemma
  where
    lemma : a · (inverse (inverse b)) ∼ 0G
    lemma = transitive (+WellDefined reflexive (invTwice b)) ab-1

transferToRight'' : {a b : A} → Setoid._∼_ S a b → (a · (inverse b)) ∼ 0G
transferToRight'' {a} {b} a~b = transitive (+WellDefined a~b reflexive) invRight

invInv : {x : A} → (inverse (inverse x)) ∼ x
invInv {x} = symmetric (transferToRight' invRight)

invIdent : (inverse 0G) ∼ 0G
invIdent = symmetric (transferToRight' identLeft)

swapInv : {x y : A} → (inverse x) ∼ y → x ∼ (inverse y)
swapInv {x} {y} -x=y = transitive (symmetric invInv) (inverseWellDefined -x=y)

identityIsUnique : (e : A) → ((b : A) → ((b · e) ∼ b)) → (e ∼ 0G)
identityIsUnique thing fb = transitive (symmetric identLeft) (fb 0G)

invContravariant : {x y : A} → (Setoid._∼_ S (Group.inverse G (x · y)) ((Group.inverse G y) · (Group.inverse G x)))
invContravariant {x} {y} = ans
  where
    _^-1 = inverse
    otherInv = (y ^-1) · (x ^-1)
    many+Associatives : x · ((y · (y ^-1)) · (x ^-1)) ∼ (x · y) · ((y ^-1) · (x ^-1))
    oneMult : (x · y) · otherInv ∼ x · (x ^-1)
    many+Associatives = transitive +Associative (transitive (+WellDefined +Associative reflexive) (symmetric +Associative))
    oneMult = symmetric (transitive (+WellDefined reflexive (transitive (symmetric identLeft) (+WellDefined (symmetric invRight) reflexive))) many+Associatives)
    otherInvIsInverse : (x · y) · otherInv ∼ 0G
    otherInvIsInverse = transitive oneMult invRight
    ans : (x · y) ^-1 ∼ (y ^-1) · (x ^-1)
    ans = symmetric (leftInversesAreUnique otherInvIsInverse)

equalsDoubleImpliesZero : {x : A} → (x · x) ∼ x → x ∼ 0G
equalsDoubleImpliesZero 2x=x = transitive (symmetric identLeft) (transitive (+WellDefined (symmetric invLeft) reflexive) (transitive (symmetric +Associative) (transitive (+WellDefined reflexive 2x=x) invLeft)))
