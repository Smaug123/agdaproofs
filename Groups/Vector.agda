{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Groups.Abelian.Definition
open import Setoids.Setoids
open import Vectors
open import Numbers.Naturals.Semiring
open import Sets.EquivalenceRelations

module Groups.Vector {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open Setoid S
open Equivalence eq
open Group G

vecEquiv : {n : ℕ} → Vec A n → Vec A n → Set b
vecEquiv {zero} [] [] = True'
vecEquiv {succ n} (x ,- v1) (y ,- v2) = (x ∼ y) && vecEquiv v1 v2

private
  vecEquivRefl : {n : ℕ} → (x : Vec A n) → vecEquiv x x
  vecEquivRefl [] = record {}
  vecEquivRefl (x ,- xs) = reflexive ,, vecEquivRefl xs

  vecEquivSymm : {n : ℕ} → (x y : Vec A n) → vecEquiv x y → vecEquiv y x
  vecEquivSymm [] [] record {} = record {}
  vecEquivSymm (x ,- xs) (y ,- ys) (fst ,, snd) = symmetric fst ,, vecEquivSymm _ _ snd

  vecEquivTrans : {n : ℕ} → (x y z : Vec A n) → vecEquiv x y → vecEquiv y z → vecEquiv x z
  vecEquivTrans [] [] [] x=y y=z = record {}
  vecEquivTrans (x ,- xs) (y ,- ys) (z ,- zs) (fst1 ,, snd1) (fst2 ,, snd2) = transitive fst1 fst2 ,, vecEquivTrans xs ys zs snd1 snd2

vectorSetoid : (n : ℕ) → Setoid (Vec A n)
Setoid._∼_ (vectorSetoid n) = vecEquiv {n}
Equivalence.reflexive (Setoid.eq (vectorSetoid n)) {x} = vecEquivRefl x
Equivalence.symmetric (Setoid.eq (vectorSetoid n)) {x} {y} = vecEquivSymm x y
Equivalence.transitive (Setoid.eq (vectorSetoid n)) {x} {y} {z} = vecEquivTrans x y z

vectorAdd : {n : ℕ} → Vec A n → Vec A n → Vec A n
vectorAdd [] [] = []
vectorAdd (x ,- v1) (y ,- v2) = (x + y) ,- (vectorAdd v1 v2)

private
  addWellDefined : {n : ℕ} → (m k x y : Vec A n) → Setoid._∼_ (vectorSetoid n) m x → Setoid._∼_ (vectorSetoid n) k y → Setoid._∼_ (vectorSetoid n) (vectorAdd m k) (vectorAdd x y)
  addWellDefined [] [] [] [] m=x k=y = record {}
  addWellDefined (m ,- ms) (k ,- ks) (x ,- xs) (y ,- ys) (m=x ,, ms=xs) (k=y ,, ks=ys) = +WellDefined m=x k=y ,, addWellDefined ms ks xs ys ms=xs ks=ys

  addAssoc : {n : ℕ} → (x y z : Vec A n) → Setoid._∼_ (vectorSetoid n) (vectorAdd x (vectorAdd y z)) (vectorAdd (vectorAdd x y) z)
  addAssoc [] [] [] = record {}
  addAssoc (x ,- xs) (y ,- ys) (z ,- zs) = +Associative ,, addAssoc xs ys zs

  vecIdentRight : {n : ℕ} → (a : Vec A n) → Setoid._∼_ (vectorSetoid n) (vectorAdd a (vecPure 0G)) a
  vecIdentRight [] = record {}
  vecIdentRight (x ,- a) = identRight ,, vecIdentRight a

  vecIdentLeft : {n : ℕ} → (a : Vec A n) → Setoid._∼_ (vectorSetoid n) (vectorAdd (vecPure 0G) a) a
  vecIdentLeft [] = record {}
  vecIdentLeft (x ,- a) = identLeft ,, vecIdentLeft a

  vecInvLeft : {n : ℕ} → (a : Vec A n) → Setoid._∼_ (vectorSetoid n) (vectorAdd (vecMap inverse a) a) (vecPure 0G)
  vecInvLeft [] = record {}
  vecInvLeft (x ,- a) = invLeft ,, vecInvLeft a

  vecInvRight : {n : ℕ} → (a : Vec A n) → Setoid._∼_ (vectorSetoid n) (vectorAdd a (vecMap inverse a)) (vecPure 0G)
  vecInvRight [] = record {}
  vecInvRight (x ,- a) = invRight ,, vecInvRight a

vectorGroup : {n : ℕ} → Group (vectorSetoid n) (vectorAdd {n})
Group.+WellDefined vectorGroup {m} {n} {x} {y} = addWellDefined m n x y
Group.0G vectorGroup = vecPure 0G
Group.inverse vectorGroup x = vecMap inverse x
Group.+Associative vectorGroup {x} {y} {z} = addAssoc x y z
Group.identRight vectorGroup {a} = vecIdentRight a
Group.identLeft vectorGroup {a} = vecIdentLeft a
Group.invLeft vectorGroup {a} = vecInvLeft a
Group.invRight vectorGroup {a} = vecInvRight a

abelianVectorGroup : {n : ℕ} → AbelianGroup G → AbelianGroup (vectorGroup {n})
AbelianGroup.commutative (abelianVectorGroup grp) {[]} {[]} = record {}
AbelianGroup.commutative (abelianVectorGroup grp) {x ,- xs} {y ,- ys} = AbelianGroup.commutative grp ,, AbelianGroup.commutative (abelianVectorGroup grp) {xs} {ys}
