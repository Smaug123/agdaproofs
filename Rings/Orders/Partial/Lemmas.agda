{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Orders.Partial.Definition


module Rings.Orders.Partial.Lemmas {n m p : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {p} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} (pRing : PartiallyOrderedRing R pOrder) where

abstract

  open PartiallyOrderedRing pRing
  open Setoid S
  open SetoidPartialOrder pOrder
  open Ring R
  open Group additiveGroup

  open import Rings.Lemmas R

  ringAddInequalities : {w x y z : A} → w < x → y < z → (w + y) < (x + z)
  ringAddInequalities {w = w} {x} {y} {z} w<x y<z = <Transitive (orderRespectsAddition w<x y) (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition y<z x))

  ringCanMultiplyByPositive : {x y c : A} → (Ring.0R R) < c → x < y → (x * c) < (y * c)
  ringCanMultiplyByPositive {x} {y} {c} 0<c x<y = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.identRight additiveGroup) q'
    where
      open Equivalence eq
      have : 0R < (y + Group.inverse additiveGroup x)
      have = SetoidPartialOrder.<WellDefined pOrder (Group.invRight additiveGroup) reflexive (orderRespectsAddition x<y (Group.inverse additiveGroup x))
      p1 : 0R < ((y * c) + ((Group.inverse additiveGroup x) * c))
      p1 = SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq *Commutative (Equivalence.transitive eq *DistributesOver+ ((Group.+WellDefined additiveGroup) *Commutative *Commutative))) (orderRespectsMultiplication have 0<c)
      p' : 0R < ((y * c) + (Group.inverse additiveGroup (x * c)))
      p' = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (Equivalence.transitive eq (Equivalence.transitive eq *Commutative ringMinusExtracts) (inverseWellDefined additiveGroup *Commutative))) p1
      q : (0R + (x * c)) < (((y * c) + (Group.inverse additiveGroup (x * c))) + (x * c))
      q = orderRespectsAddition p' (x * c)
      q' : (x * c) < ((y * c) + 0R)
      q' = SetoidPartialOrder.<WellDefined pOrder (Group.identLeft additiveGroup) (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup))) q

  ringMultiplyPositives : {x y a b : A} → 0R < x → 0R < a → (x < y) → (a < b) → (x * a) < (y * b)
  ringMultiplyPositives {x} {y} {a} {b} 0<x 0<a x<y a<b = SetoidPartialOrder.<Transitive pOrder (ringCanMultiplyByPositive 0<a x<y) (<WellDefined *Commutative *Commutative (ringCanMultiplyByPositive (SetoidPartialOrder.<Transitive pOrder 0<x x<y) a<b))

  ringSwapNegatives : {x y : A} → (Group.inverse (Ring.additiveGroup R) x) < (Group.inverse (Ring.additiveGroup R) y) → y < x
  ringSwapNegatives {x} {y} -x<-y = SetoidPartialOrder.<WellDefined pOrder (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup)) (Group.identRight additiveGroup))) (Group.identLeft additiveGroup) v
    where
      open Equivalence eq
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
