{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Setoids
open import Functions.Definition
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Rings.Orders.Partial.Lemmas {n m p : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {p} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} (pRing : PartiallyOrderedRing R pOrder) where

abstract

  open PartiallyOrderedRing pRing
  open Setoid S
  open SetoidPartialOrder pOrder
  open Ring R
  open Group additiveGroup
  open Equivalence eq

  open import Rings.Lemmas R

  ringAddInequalities : {w x y z : A} → w < x → y < z → (w + y) < (x + z)
  ringAddInequalities {w = w} {x} {y} {z} w<x y<z = <Transitive (orderRespectsAddition w<x y) (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition y<z x))

  ringCanMultiplyByPositive : {x y c : A} → (Ring.0R R) < c → x < y → (x * c) < (y * c)
  ringCanMultiplyByPositive {x} {y} {c} 0<c x<y = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.identRight additiveGroup) q'
    where
      have : 0R < (y + Group.inverse additiveGroup x)
      have = SetoidPartialOrder.<WellDefined pOrder (Group.invRight additiveGroup) reflexive (orderRespectsAddition x<y (Group.inverse additiveGroup x))
      p1 : 0R < ((y * c) + ((Group.inverse additiveGroup x) * c))
      p1 = SetoidPartialOrder.<WellDefined pOrder reflexive (transitive *Commutative (transitive *DistributesOver+ ((Group.+WellDefined additiveGroup) *Commutative *Commutative))) (orderRespectsMultiplication have 0<c)
      p' : 0R < ((y * c) + (Group.inverse additiveGroup (x * c)))
      p' = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (transitive (transitive *Commutative ringMinusExtracts) (inverseWellDefined additiveGroup *Commutative))) p1
      q : (0R + (x * c)) < (((y * c) + (Group.inverse additiveGroup (x * c))) + (x * c))
      q = orderRespectsAddition p' (x * c)
      q' : (x * c) < ((y * c) + 0R)
      q' = SetoidPartialOrder.<WellDefined pOrder (Group.identLeft additiveGroup) (transitive (symmetric (Group.+Associative additiveGroup)) (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup))) q

  ringCanMultiplyByPositive' : {x y c : A} → (Ring.0R R) < c → x < y → (c * x) < (c * y)
  ringCanMultiplyByPositive' {x} {y} {c} 0<c x<y = SetoidPartialOrder.<WellDefined pOrder *Commutative *Commutative (ringCanMultiplyByPositive 0<c x<y)

  ringMultiplyPositives : {x y a b : A} → 0R < x → 0R < a → (x < y) → (a < b) → (x * a) < (y * b)
  ringMultiplyPositives {x} {y} {a} {b} 0<x 0<a x<y a<b = SetoidPartialOrder.<Transitive pOrder (ringCanMultiplyByPositive 0<a x<y) (<WellDefined *Commutative *Commutative (ringCanMultiplyByPositive (SetoidPartialOrder.<Transitive pOrder 0<x x<y) a<b))

  ringSwapNegatives : {x y : A} → (Group.inverse (Ring.additiveGroup R) x) < (Group.inverse (Ring.additiveGroup R) y) → y < x
  ringSwapNegatives {x} {y} -x<-y = SetoidPartialOrder.<WellDefined pOrder (transitive (symmetric (Group.+Associative additiveGroup)) (transitive (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup)) (Group.identRight additiveGroup))) (Group.identLeft additiveGroup) v
    where
      t : ((Group.inverse additiveGroup x) + y) < ((Group.inverse additiveGroup y) + y)
      t = orderRespectsAddition -x<-y y
      u : (y + (Group.inverse additiveGroup x)) < 0R
      u = SetoidPartialOrder.<WellDefined pOrder (groupIsAbelian) (Group.invLeft additiveGroup) t
      v : ((y + (Group.inverse additiveGroup x)) + x) < (0R + x)
      v = orderRespectsAddition u x

  ringSwapNegatives' : {x y : A} → x < y → (Group.inverse (Ring.additiveGroup R) y) < (Group.inverse (Ring.additiveGroup R) x)
  ringSwapNegatives' {x} {y} x<y = ringSwapNegatives (<WellDefined (Equivalence.symmetric eq (invTwice additiveGroup _)) (Equivalence.symmetric eq (invTwice additiveGroup _)) x<y)

  ringCanMultiplyByNegative : {x y c : A} → c < (Ring.0R R) → x < y → (y * c) < (x * c)
  ringCanMultiplyByNegative {x} {y} {c} c<0 x<y = ringSwapNegatives u
    where
    open Equivalence eq
    p1 : (c + Group.inverse additiveGroup c) < (0R + Group.inverse additiveGroup c)
    p1 = orderRespectsAddition c<0 _
    0<-c : 0R < (Group.inverse additiveGroup c)
    0<-c = SetoidPartialOrder.<WellDefined pOrder (Group.invRight additiveGroup) (Group.identLeft additiveGroup) p1
    t : (x * Group.inverse additiveGroup c) < (y * Group.inverse additiveGroup c)
    t = ringCanMultiplyByPositive 0<-c x<y
    u : (Group.inverse additiveGroup (x * c)) < Group.inverse additiveGroup (y * c)
    u = SetoidPartialOrder.<WellDefined pOrder ringMinusExtracts ringMinusExtracts t

  anyComparisonImpliesNontrivial : {a b : A} → a < b → (0R ∼ 1R) → False
  anyComparisonImpliesNontrivial {a} {b} a<b 0=1 = irreflexive (<WellDefined (oneZeroImpliesAllZero 0=1) (oneZeroImpliesAllZero 0=1) a<b)

  moveInequality : {a b : A} → a < b → 0R < (b + inverse a)
  moveInequality {a} {b} a<b = <WellDefined invRight reflexive (orderRespectsAddition a<b (inverse a))

  moveInequality' : {a b : A} → a < b → (a + inverse b) < 0R
  moveInequality' {a} {b} a<b = <WellDefined reflexive invRight (orderRespectsAddition a<b (inverse b))

  greaterImpliesNotEqual : {a b : A} → a < b → (a ∼ b → False)
  greaterImpliesNotEqual {a} {b} a<b a=b = irreflexive (<WellDefined a=b reflexive a<b)

  greaterImpliesNotEqual' : {a b : A} → a < b → (b ∼ a → False)
  greaterImpliesNotEqual' {a} {b} a<b a=b = irreflexive (<WellDefined reflexive a=b a<b)

  negativeInequality : {a : A} → a < 0G → 0G < inverse a
  negativeInequality {a} a<0 = <WellDefined invRight identLeft (orderRespectsAddition a<0 (inverse a))

  negativeInequality' : {a : A} → 0G < a → inverse a < 0G
  negativeInequality' {a} 0<a = <WellDefined identLeft invRight (orderRespectsAddition 0<a (inverse a))

open import Rings.InitialRing R

fromNIncreasing : (0R < 1R) → (n : ℕ) → (fromN n) < (fromN (succ n))
fromNIncreasing 0<1 zero = <WellDefined reflexive (symmetric identRight) 0<1
fromNIncreasing 0<1 (succ n) = <WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (fromNIncreasing 0<1 n) 1R)

fromNPreservesOrder : (0R < 1R) → {a b : ℕ} → (a <N b) → (fromN a) < (fromN b)
fromNPreservesOrder 0<1 {zero} {succ zero} a<b = fromNIncreasing 0<1 0
fromNPreservesOrder 0<1 {zero} {succ (succ b)} a<b = <Transitive (fromNPreservesOrder 0<1 (succIsPositive b)) (fromNIncreasing 0<1 (succ b))
fromNPreservesOrder 0<1 {succ a} {succ b} a<b = <WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (fromNPreservesOrder 0<1 (canRemoveSuccFrom<N a<b)) 1R)
