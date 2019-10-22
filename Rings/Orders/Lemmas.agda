{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Lemmas
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Order

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Orders.Lemmas {n m p : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {p} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (order : OrderedRing R tOrder) where

open OrderedRing order
open Setoid S
open SetoidPartialOrder pOrder
open SetoidTotalOrder tOrder
open Ring R
open Group additiveGroup

open import Rings.Lemmas R


ringAddInequalities : {w x y z : A} → w < x → y < z → (w + y) < (x + z)
ringAddInequalities {w = w} {x} {y} {z} w<x y<z = transitive (orderRespectsAddition w<x y) (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition y<z x))

lemm2 : (a : A) → a < 0G → 0G < inverse a
lemm2 a a<0 with SetoidTotalOrder.totality tOrder 0R (inverse a)
lemm2 a a<0 | inl (inl 0<-a) = 0<-a
lemm2 a a<0 | inl (inr -a<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder (<WellDefined (invLeft {a}) (identLeft {a}) (orderRespectsAddition -a<0 a)) a<0))
lemm2 a a<0 | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq identRight) t) (Equivalence.reflexive eq) a<0))
  where
    t : a + 0G ∼ 0G
    t = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) 0=-a) (invRight {a})

lemm2' : (a : A) → 0G < a → inverse a < 0G
lemm2' a 0<a with SetoidTotalOrder.totality tOrder 0R (inverse a)
lemm2' a 0<a | inl (inl 0<-a) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder 0<a (<WellDefined (identLeft {a}) (invLeft {a}) (orderRespectsAddition 0<-a a))))
lemm2' a 0<a | inl (inr -a<0) = -a<0
lemm2' a 0<a | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.symmetric eq identRight) t) 0<a))
  where
    t : a + 0G ∼ 0G
    t = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) 0=-a) (invRight {a})

lemm3 : (a b : A) → 0G ∼ (a + b) → 0G ∼ a → 0G ∼ b
lemm3 a b pr1 pr2 with transferToRight' additiveGroup (Equivalence.symmetric eq pr1)
... | a=-b with Equivalence.transitive eq pr2 a=-b
... | 0=-b with inverseWellDefined additiveGroup 0=-b
... | -0=--b = Equivalence.transitive eq (Equivalence.symmetric eq (invIdentity additiveGroup)) (Equivalence.transitive eq -0=--b (invTwice additiveGroup b))


triangleInequality : (a b : A) → ((abs (a + b)) < ((abs a) + (abs b))) || (abs (a + b) ∼ (abs a) + (abs b))
triangleInequality a b with totality 0R (a + b)
triangleInequality a b | inl (inl 0<a+b) with totality 0R a
triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) with totality 0R b
triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) | inl (inl 0<b) = inr (Equivalence.reflexive eq)
triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) | inl (inr b<0) = inl (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.transitive pOrder b<0 (lemm2 b b<0)) a))
triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) | inr 0=b = inr (Equivalence.reflexive eq)
triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) with totality 0R b
triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) | inl (inl 0<b) = inl (orderRespectsAddition (SetoidPartialOrder.transitive pOrder a<0 (lemm2 a a<0)) b)
triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) | inl (inr b<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder 0<a+b (<WellDefined (Equivalence.reflexive eq) identLeft (ringAddInequalities a<0 b<0))))
triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) | inr 0=b = inl (orderRespectsAddition (SetoidPartialOrder.transitive pOrder a<0 (lemm2 a a<0)) b)
triangleInequality a b | inl (inl 0<a+b) | inr 0=a with totality 0R b
triangleInequality a b | inl (inl 0<a+b) | inr 0=a | inl (inl 0<b) = inr (Equivalence.reflexive eq)
triangleInequality a b | inl (inl 0<a+b) | inr 0=a | inl (inr b<0) = inl (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.transitive pOrder b<0 (lemm2 b b<0)) a))
triangleInequality a b | inl (inl 0<a+b) | inr 0=a | inr 0=b = inr (Equivalence.reflexive eq)
triangleInequality a b | inl (inr a+b<0) with totality 0G a
triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) with totality 0G b
triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) | inl (inl 0<b) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities 0<a 0<b)) a+b<0))
triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) | inl (inr b<0) = inl (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq (invContravariant additiveGroup)) (inverseWellDefined additiveGroup groupIsAbelian)) (Equivalence.reflexive eq) (orderRespectsAddition (SetoidPartialOrder.transitive pOrder (lemm2' _ 0<a) 0<a) (inverse b)))
triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) | inr 0=b = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder 0<a (<WellDefined (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) identRight) (Equivalence.reflexive eq) a+b<0)))
triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) with totality 0G b
triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) | inl (inl 0<b) = inl (<WellDefined (Equivalence.symmetric eq (invContravariant additiveGroup)) groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.transitive pOrder (lemm2' _ 0<b) 0<b) (inverse a)))
triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) | inl (inr b<0) = inr (Equivalence.transitive eq (invContravariant additiveGroup) groupIsAbelian)
triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) | inr 0=b = inr (Equivalence.transitive eq (invContravariant additiveGroup) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (+WellDefined (Equivalence.transitive eq (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=b)) (invIdentity additiveGroup)) (Equivalence.reflexive eq)) identLeft) (Equivalence.symmetric eq identRight)) (+WellDefined (Equivalence.reflexive eq) 0=b)))
triangleInequality a b | inl (inr a+b<0) | inr 0=a with totality 0G b
triangleInequality a b | inl (inr a+b<0) | inr 0=a | inl (inl 0<b) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder 0<b (<WellDefined (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.reflexive eq)) identLeft) (Equivalence.reflexive eq) a+b<0)))
triangleInequality a b | inl (inr a+b<0) | inr 0=a | inl (inr b<0) = inr (Equivalence.transitive eq (invContravariant additiveGroup) (Equivalence.transitive eq groupIsAbelian (+WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq (inverseWellDefined additiveGroup 0=a)) (invIdentity additiveGroup)) 0=a) (Equivalence.reflexive eq))))
triangleInequality a b | inl (inr a+b<0) | inr 0=a | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.symmetric eq 0=b)) identLeft) (Equivalence.reflexive eq) a+b<0))
triangleInequality a b | inr 0=a+b with totality 0G a
triangleInequality a b | inr 0=a+b | inl (inl 0<a) with totality 0G b
triangleInequality a b | inr 0=a+b | inl (inl 0<a) | inl (inl 0<b) = exFalso (irreflexive {0G} (<WellDefined identLeft (Equivalence.symmetric eq 0=a+b) (ringAddInequalities 0<a 0<b)))
triangleInequality a b | inr 0=a+b | inl (inl 0<a) | inl (inr b<0) = inl (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.transitive pOrder b<0 (lemm2 _ b<0)) a))
triangleInequality a b | inr 0=a+b | inl (inl 0<a) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (lemm3 _ _ (Equivalence.transitive eq 0=a+b groupIsAbelian) 0=b)) 0<a))
triangleInequality a b | inr 0=a+b | inl (inr a<0) with totality 0G b
triangleInequality a b | inr 0=a+b | inl (inr a<0) | inl (inl 0<b) = inl (orderRespectsAddition (SetoidPartialOrder.transitive pOrder a<0 (lemm2 _ a<0)) b)
triangleInequality a b | inr 0=a+b | inl (inr a<0) | inl (inr b<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq 0=a+b) identLeft (ringAddInequalities a<0 b<0)))
triangleInequality a b | inr 0=a+b | inl (inr a<0) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (lemm3 _ _ (Equivalence.transitive eq 0=a+b groupIsAbelian) 0=b)) (Equivalence.reflexive eq) a<0))
triangleInequality a b | inr 0=a+b | inr 0=a with totality 0G b
triangleInequality a b | inr 0=a+b | inr 0=a | inl (inl 0<b) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (lemm3 a b 0=a+b 0=a)) 0<b))
triangleInequality a b | inr 0=a+b | inr 0=a | inl (inr b<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (lemm3 a b 0=a+b 0=a)) (Equivalence.reflexive eq) b<0))
triangleInequality a b | inr 0=a+b | inr 0=a | inr 0=b = inr (Equivalence.reflexive eq)

ringMinusFlipsOrder : {x : A} → (Ring.0R R) < x → (Group.inverse (Ring.additiveGroup R) x) < (Ring.0R R)
ringMinusFlipsOrder {x = x} 0<x with SetoidTotalOrder.totality tOrder (Ring.0R R) (Group.inverse (Ring.additiveGroup R) x)
ringMinusFlipsOrder {x} 0<x | inl (inl 0<inv) = exFalso (SetoidPartialOrder.irreflexive pOrder bad')
  where
    bad : (Group.0G (Ring.additiveGroup R) + Group.0G (Ring.additiveGroup R)) < (x + Group.inverse (Ring.additiveGroup R) x)
    bad = ringAddInequalities 0<x 0<inv
    bad' : (Group.0G (Ring.additiveGroup R)) < (Group.0G (Ring.additiveGroup R))
    bad' = SetoidPartialOrder.<WellDefined pOrder (Group.identRight (Ring.additiveGroup R)) (Group.invRight (Ring.additiveGroup R)) bad
ringMinusFlipsOrder {x} 0<x | inl (inr inv<0) = inv<0
ringMinusFlipsOrder {x} 0<x | inr 0=inv = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (Equivalence.reflexive (Setoid.eq S)) (groupLemmaMove0G (Ring.additiveGroup R) 0=inv) 0<x))

ringMinusFlipsOrder' : {x : A} → (Group.inverse (Ring.additiveGroup R) x) < (Ring.0R R) → (Ring.0R R) < x
ringMinusFlipsOrder' {x} -x<0 with SetoidTotalOrder.totality tOrder (Ring.0R R) x
ringMinusFlipsOrder' {x} -x<0 | inl (inl 0<x) = 0<x
ringMinusFlipsOrder' {x} -x<0 | inl (inr x<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (Group.invLeft (Ring.additiveGroup R)) (Group.identRight (Ring.additiveGroup R)) bad))
  where
    bad : ((Group.inverse (Ring.additiveGroup R) x) + x) < (Group.0G (Ring.additiveGroup R) + Group.0G (Ring.additiveGroup R))
    bad = ringAddInequalities -x<0 x<0
ringMinusFlipsOrder' {x} -x<0 | inr 0=x = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (symmetric (groupLemmaMove0G' (Ring.additiveGroup R) (symmetric 0=x))) (Equivalence.reflexive (Setoid.eq S)) -x<0))
  where
    open Equivalence eq

ringMinusFlipsOrder'' : {x : A} → x < (Ring.0R R) → (Ring.0R R) < Group.inverse (Ring.additiveGroup R) x
ringMinusFlipsOrder'' {x} x<0 = ringMinusFlipsOrder' (SetoidPartialOrder.<WellDefined pOrder {x} {Group.inverse (Ring.additiveGroup R) (Group.inverse (Ring.additiveGroup R) x)} {Ring.0R R} {Ring.0R R} (Equivalence.symmetric (Setoid.eq S) (invInv (Ring.additiveGroup R))) (Equivalence.reflexive (Setoid.eq S)) x<0)

ringMinusFlipsOrder''' : {x : A} → (Ring.0R R) < (Group.inverse (Ring.additiveGroup R) x) → x < (Ring.0R R)
ringMinusFlipsOrder''' {x} 0<-x = SetoidPartialOrder.<WellDefined pOrder (invInv (Ring.additiveGroup R)) (Equivalence.reflexive (Setoid.eq S)) (ringMinusFlipsOrder 0<-x)

ringCanMultiplyByPositive : {x y c : A} → (Ring.0R R) < c → x < y → (x * c) < (y * c)
ringCanMultiplyByPositive {x} {y} {c} 0<c x<y = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.identRight additiveGroup) q'
  where
    open Equivalence eq
    have : 0R < (y + Group.inverse additiveGroup x)
    have = SetoidPartialOrder.<WellDefined pOrder (Group.invRight additiveGroup) reflexive (OrderedRing.orderRespectsAddition order x<y (Group.inverse additiveGroup x))
    p1 : 0R < ((y * c) + ((Group.inverse additiveGroup x) * c))
    p1 = SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq *Commutative (Equivalence.transitive eq *DistributesOver+ ((Group.+WellDefined additiveGroup) *Commutative *Commutative))) (OrderedRing.orderRespectsMultiplication order have 0<c)
    p' : 0R < ((y * c) + (Group.inverse additiveGroup (x * c)))
    p' = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (Equivalence.transitive eq (Equivalence.transitive eq *Commutative ringMinusExtracts) (inverseWellDefined additiveGroup *Commutative))) p1
    q : (0R + (x * c)) < (((y * c) + (Group.inverse additiveGroup (x * c))) + (x * c))
    q = OrderedRing.orderRespectsAddition order p' (x * c)
    q' : (x * c) < ((y * c) + 0R)
    q' = SetoidPartialOrder.<WellDefined pOrder (Group.identLeft additiveGroup) (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup))) q

ringCanCancelPositive : {x y c : A} → (Ring.0R R) < c → (x * c) < (y * c) → x < y
ringCanCancelPositive {x} {y} {c} 0<c xc<yc = SetoidPartialOrder.<WellDefined pOrder (Group.identLeft additiveGroup) (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup)) (Group.identRight additiveGroup))) q''
  where
    open Equivalence (Setoid.eq S)
    have : 0R < ((y * c) + (Group.inverse additiveGroup (x * c)))
    have = SetoidPartialOrder.<WellDefined pOrder (Group.invRight additiveGroup) reflexive (OrderedRing.orderRespectsAddition order xc<yc (Group.inverse additiveGroup _))
    p1 : 0R < ((y * c) + ((Group.inverse additiveGroup x) * c))
    p1 = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (symmetric (Equivalence.transitive eq (*Commutative) (Equivalence.transitive eq ringMinusExtracts (inverseWellDefined additiveGroup *Commutative))))) have
    q : 0R < ((y + Group.inverse additiveGroup x) * c)
    q = SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq (Equivalence.transitive eq (Group.+WellDefined additiveGroup *Commutative *Commutative) (symmetric *DistributesOver+)) *Commutative) p1
    q' : 0R < (y + Group.inverse additiveGroup x)
    q' with SetoidTotalOrder.totality tOrder 0R (y + Group.inverse additiveGroup x)
    q' | inl (inl pr) = pr
    q' | inl (inr y-x<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq *Commutative (Ring.timesZero R)) k))
      where
        f : ((y + inverse x) + (inverse (y + inverse x))) < (0G + inverse (y + inverse x))
        f = OrderedRing.orderRespectsAddition order y-x<0 _
        g : 0G < inverse (y + inverse x)
        g = SetoidPartialOrder.<WellDefined pOrder invRight identLeft f
        h : (0G * c) < ((inverse (y + inverse x)) * c)
        h = ringCanMultiplyByPositive 0<c g
        i : (0R + (0G * c)) < (((y + inverse x) * c) + ((inverse (y + inverse x)) * c))
        i = ringAddInequalities q h
        j : 0R < (((y + inverse x) + (inverse (y + inverse x))) * c)
        j = SetoidPartialOrder.<WellDefined pOrder (Equivalence.transitive eq identLeft (Equivalence.transitive eq *Commutative (Ring.timesZero R))) (symmetric (Equivalence.transitive eq *Commutative (Equivalence.transitive eq *DistributesOver+ (Group.+WellDefined additiveGroup *Commutative *Commutative)))) i
        k : 0R < (0R * c)
        k = SetoidPartialOrder.<WellDefined pOrder reflexive (*WellDefined invRight reflexive) j
    q' | inr 0=y-x = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (*WellDefined x=y reflexive) reflexive xc<yc))
      where
        f : inverse 0G ∼ inverse (y + inverse x)
        f = inverseWellDefined additiveGroup 0=y-x
        g : 0G ∼ (inverse y) + x
        g = Equivalence.transitive eq (symmetric (invIdentity additiveGroup)) (Equivalence.transitive eq f (Equivalence.transitive eq (Equivalence.transitive eq (invContravariant additiveGroup) groupIsAbelian) (+WellDefined reflexive (invInv additiveGroup))))
        x=y : x ∼ y
        x=y = transferToRight additiveGroup (symmetric (Equivalence.transitive eq g groupIsAbelian))
    q'' : (0R + x) < ((y + Group.inverse additiveGroup x) + x)
    q'' = OrderedRing.orderRespectsAddition order q' x

ringSwapNegatives : {x y : A} → (Group.inverse (Ring.additiveGroup R) x) < (Group.inverse (Ring.additiveGroup R) y) → y < x
ringSwapNegatives {x} {y} -x<-y = SetoidPartialOrder.<WellDefined pOrder (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup)) (Group.identRight additiveGroup))) (Group.identLeft additiveGroup) v
  where
    open Equivalence eq
    t : ((Group.inverse additiveGroup x) + y) < ((Group.inverse additiveGroup y) + y)
    t = OrderedRing.orderRespectsAddition order -x<-y y
    u : (y + (Group.inverse additiveGroup x)) < 0R
    u = SetoidPartialOrder.<WellDefined pOrder (groupIsAbelian) (Group.invLeft additiveGroup) t
    v : ((y + (Group.inverse additiveGroup x)) + x) < (0R + x)
    v = OrderedRing.orderRespectsAddition order u x

ringCanMultiplyByNegative : {x y c : A} → c < (Ring.0R R) → x < y → (y * c) < (x * c)
ringCanMultiplyByNegative {x} {y} {c} c<0 x<y = ringSwapNegatives u
  where
    open Equivalence eq
    p1 : (c + Group.inverse additiveGroup c) < (0R + Group.inverse additiveGroup c)
    p1 = OrderedRing.orderRespectsAddition order c<0 _
    0<-c : 0R < (Group.inverse additiveGroup c)
    0<-c = SetoidPartialOrder.<WellDefined pOrder (Group.invRight additiveGroup) (Group.identLeft additiveGroup) p1
    t : (x * Group.inverse additiveGroup c) < (y * Group.inverse additiveGroup c)
    t = ringCanMultiplyByPositive 0<-c x<y
    u : (Group.inverse additiveGroup (x * c)) < Group.inverse additiveGroup (y * c)
    u = SetoidPartialOrder.<WellDefined pOrder ringMinusExtracts ringMinusExtracts t

ringCanCancelNegative : {x y c : A} → c < (Ring.0R R) → (x * c) < (y * c) → y < x
ringCanCancelNegative {x} {y} {c} c<0 xc<yc = r
  where
    open Equivalence eq
    p0 : 0R < ((y * c) + inverse (x * c))
    p0 = SetoidPartialOrder.<WellDefined pOrder invRight reflexive (OrderedRing.orderRespectsAddition order xc<yc (inverse (x * c)))
    p1 : 0R < ((y * c) + ((inverse x) * c))
    p1 = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (Equivalence.transitive eq (inverseWellDefined additiveGroup *Commutative) (Equivalence.transitive eq (symmetric ringMinusExtracts) *Commutative))) p0
    p2 : 0R < ((y + inverse x) * c)
    p2 = SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq (Group.+WellDefined additiveGroup *Commutative *Commutative) (Equivalence.transitive eq (symmetric *DistributesOver+) *Commutative)) p1
    q : (y + inverse x) < 0R
    q with SetoidTotalOrder.totality tOrder 0R (y + inverse x)
    q | inl (inl pr) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder bad c<0))
      where
        bad : 0R < c
        bad = ringCanCancelPositive pr (SetoidPartialOrder.<WellDefined pOrder (symmetric (Equivalence.transitive eq *Commutative (Ring.timesZero R))) *Commutative p2)
    q | inl (inr pr) = pr
    q | inr 0=y-x = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (*WellDefined x=y reflexive) reflexive xc<yc))
      where
        x=y : x ∼ y
        x=y = Equivalence.transitive eq (symmetric identLeft) (Equivalence.transitive eq (Group.+WellDefined additiveGroup 0=y-x reflexive) (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive invLeft) identRight)))
    r : y < x
    r = SetoidPartialOrder.<WellDefined pOrder (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive (invLeft)) identRight)) (Group.identLeft additiveGroup) (OrderedRing.orderRespectsAddition order q x)

absZero : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {a} {c} A} {p : SetoidPartialOrder S _<_} {t : SetoidTotalOrder p} (o : OrderedRing R t) → OrderedRing.abs o (Ring.0R R) ≡ Ring.0R R
absZero {R = R} {t = t} oR with SetoidTotalOrder.totality t (Ring.0R R) (Ring.0R R)
absZero {R = R} {t = t} oR | inl (inl x) = exFalso (SetoidPartialOrder.irreflexive (SetoidTotalOrder.partial t) x)
absZero {R = R} {t = t} oR | inl (inr x) = exFalso (SetoidPartialOrder.irreflexive (SetoidTotalOrder.partial t) x)
absZero {R = R} {t = t} oR | inr x = refl

absNegation : (a : A) → (abs a) ∼ (abs (inverse a))
absNegation a with totality 0R a
absNegation a | inl (inl 0<a) with totality 0G (inverse a)
absNegation a | inl (inl 0<a) | inl (inl 0<-a) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder 0<-a (lemm2' a 0<a)))
absNegation a | inl (inl 0<a) | inl (inr -a<0) = Equivalence.symmetric eq (invTwice additiveGroup a)
absNegation a | inl (inl 0<a) | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq (invTwice additiveGroup a)) (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=-a))) (invIdent additiveGroup)) 0<a))
absNegation a | inl (inr a<0) with totality 0G (inverse a)
absNegation a | inl (inr a<0) | inl (inl 0<-a) = Equivalence.reflexive eq
absNegation a | inl (inr a<0) | inl (inr -a<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder (<WellDefined (Equivalence.reflexive eq) (invTwice additiveGroup a) (lemm2 (inverse a) -a<0)) a<0))
absNegation a | inl (inr a<0) | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq (Equivalence.transitive eq (inverseWellDefined additiveGroup 0=-a) (invTwice additiveGroup a))) (invIdent additiveGroup)) (Equivalence.reflexive eq) a<0))
absNegation a | inr 0=a with totality 0G (inverse a)
absNegation a | inr 0=a | inl (inl 0<-a) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=a)) (invIdent additiveGroup)) 0<-a))
absNegation a | inr 0=a | inl (inr -a<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=a)) (invIdent additiveGroup)) (Equivalence.reflexive eq) -a<0))
absNegation a | inr 0=a | inr 0=-a = Equivalence.transitive eq (Equivalence.symmetric eq 0=a) 0=-a

lemm4 : (a b : A) → (0G < a) → (b < 0G) → (a * b) < 0G
lemm4 a b 0<a b<0 with orderRespectsMultiplication 0<a (lemm2 _ b<0)
... | bl = <WellDefined (invTwice additiveGroup _) (Equivalence.reflexive eq) (lemm2' _ (<WellDefined (Equivalence.reflexive eq) ringMinusExtracts bl))

lemm5 : (a b : A) → (a < 0G) → (b < 0G) → 0G < (a * b)
lemm5 a b a<0 b<0 with orderRespectsMultiplication (lemm2 _ a<0) (lemm2 _ b<0)
... | bl = <WellDefined (Equivalence.reflexive eq) twoNegativesTimes bl

absRespectsTimes : (a b : A) → abs (a * b) ∼ (abs a) * (abs b)
absRespectsTimes a b with totality 0R a
absRespectsTimes a b | inl (inl 0<a) with totality 0R b
absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) with totality 0R (a * b)
absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) | inl (inl 0<ab) = Equivalence.reflexive eq
absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) | inl (inr ab<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder (orderRespectsMultiplication 0<a 0<b) ab<0))
absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) | inr 0=ab = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=ab) (orderRespectsMultiplication 0<a 0<b)))
absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) with totality 0R (a * b)
absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) | inl (inl 0<ab) with <WellDefined (Equivalence.reflexive eq) ringMinusExtracts (orderRespectsMultiplication 0<a (lemm2 b b<0))
... | bl = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder 0<ab (<WellDefined (invTwice additiveGroup _) (Equivalence.reflexive eq) (lemm2' _ bl))))
absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) | inl (inr ab<0) = Equivalence.symmetric eq ringMinusExtracts
absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) | inr 0=ab = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq 0=ab) (Equivalence.reflexive eq) (lemm4 a b 0<a b<0)))
absRespectsTimes a b | inl (inl 0<a) | inr 0=b with totality 0R (a * b)
absRespectsTimes a b | inl (inl 0<a) | inr 0=b | inl (inl 0<ab) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) (timesZero {a})) 0<ab))
absRespectsTimes a b | inl (inl 0<a) | inr 0=b | inl (inr ab<0) = exFalso ((irreflexive {0G} (<WellDefined (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) (timesZero {a})) (Equivalence.reflexive eq) ab<0)))
absRespectsTimes a b | inl (inl 0<a) | inr 0=b | inr 0=ab = Equivalence.reflexive eq
absRespectsTimes a b | inl (inr a<0) with totality 0R b
absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) with totality 0R (a * b)
absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) | inl (inl 0<ab) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder 0<ab (<WellDefined *Commutative (Equivalence.reflexive eq) (lemm4 b a 0<b a<0))))
absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) | inl (inr ab<0) = Equivalence.symmetric eq ringMinusExtracts'
absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) | inr 0=ab = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq 0=ab *Commutative)) (Equivalence.reflexive eq) (lemm4 b a 0<b a<0)))
absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) with totality 0R (a * b)
absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) | inl (inl 0<ab) = Equivalence.symmetric eq twoNegativesTimes
absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) | inl (inr ab<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.transitive pOrder (lemm5 a b a<0 b<0) ab<0))
absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) | inr 0=ab = exFalso (exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=ab) (lemm5 a b a<0 b<0))))
absRespectsTimes a b | inl (inr a<0) | inr 0=b with totality 0R (a * b)
absRespectsTimes a b | inl (inr a<0) | inr 0=b | inl (inl 0<ab) = exFalso (irreflexive {0R} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) (timesZero {a})) 0<ab))
absRespectsTimes a b | inl (inr a<0) | inr 0=b | inl (inr ab<0) = exFalso (irreflexive {0R} (<WellDefined (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) timesZero) (Equivalence.reflexive eq) ab<0))
absRespectsTimes a b | inl (inr a<0) | inr 0=b | inr 0=ab = Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) (Equivalence.transitive eq (Equivalence.transitive eq timesZero (Equivalence.symmetric eq timesZero)) (*WellDefined (Equivalence.reflexive eq) 0=b))
absRespectsTimes a b | inr 0=a with totality 0R b
absRespectsTimes a b | inr 0=a | inl (inl 0<b) with totality 0R (a * b)
absRespectsTimes a b | inr 0=a | inl (inl 0<b) | inl (inl 0<ab) = Equivalence.reflexive eq
absRespectsTimes a b | inr 0=a | inl (inl 0<b) | inl (inr ab<0) = Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (inverseWellDefined additiveGroup (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.reflexive eq)) (Equivalence.transitive eq *Commutative timesZero))) (invIdent additiveGroup)) (Equivalence.transitive eq (Equivalence.symmetric eq timesZero) *Commutative)) (*WellDefined 0=a (Equivalence.reflexive eq))
absRespectsTimes a b | inr 0=a | inl (inl 0<b) | inr 0=ab = Equivalence.reflexive eq
absRespectsTimes a b | inr 0=a | inl (inr b<0) with totality 0R (a * b)
absRespectsTimes a b | inr 0=a | inl (inr b<0) | inl (inl 0<ab) = Equivalence.transitive eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.reflexive eq)) *Commutative) (Equivalence.transitive eq timesZero (Equivalence.transitive eq (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative timesZero)) (*WellDefined 0=a (Equivalence.reflexive eq))))
absRespectsTimes a b | inr 0=a | inl (inr b<0) | inl (inr ab<0) = Equivalence.symmetric eq ringMinusExtracts
absRespectsTimes a b | inr 0=a | inl (inr b<0) | inr 0=ab = Equivalence.transitive eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.reflexive eq)) *Commutative) (Equivalence.transitive eq timesZero (Equivalence.transitive eq (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative timesZero)) (*WellDefined 0=a (Equivalence.reflexive eq))))
absRespectsTimes a b | inr 0=a | inr 0=b with totality 0R (a * b)
absRespectsTimes a b | inr 0=a | inr 0=b | inl (inl 0<ab) = exFalso (irreflexive {0R} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) timesZero) 0<ab))
absRespectsTimes a b | inr 0=a | inr 0=b | inl (inr ab<0) = exFalso (irreflexive {0R} (<WellDefined (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) timesZero) (Equivalence.reflexive eq) ab<0))
absRespectsTimes a b | inr 0=a | inr 0=b | inr 0=ab = Equivalence.reflexive eq
