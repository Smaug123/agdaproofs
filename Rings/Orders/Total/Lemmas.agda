{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Rings.Orders.Total.Lemmas {n m p : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} {pOrderRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pOrderRing) where

open Ring R
open Group additiveGroup
open Setoid S
open SetoidPartialOrder pOrder
open TotallyOrderedRing order
open SetoidTotalOrder total
open PartiallyOrderedRing pOrderRing
open import Rings.Lemmas R
open import Rings.Orders.Partial.Lemmas pOrderRing

abs : A → A
abs a with totality 0R a
abs a | inl (inl 0<a) = a
abs a | inl (inr a<0) = inverse a
abs a | inr 0=a = a

abstract
  absWellDefined : (a b : A) → a ∼ b → abs a ∼ abs b
  absWellDefined a b a=b with totality 0R a
  absWellDefined a b a=b | inl (inl 0<a) with totality 0R b
  absWellDefined a b a=b | inl (inl 0<a) | inl (inl 0<b) = a=b
  absWellDefined a b a=b | inl (inl 0<a) | inl (inr b<0) = exFalso (irreflexive {0G} (<Transitive 0<a (<WellDefined (Equivalence.symmetric eq a=b) (Equivalence.reflexive eq) b<0)))
  absWellDefined a b a=b | inl (inl 0<a) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq a=b (Equivalence.symmetric eq 0=b)) 0<a))
  absWellDefined a b a=b | inl (inr a<0) with totality 0R b
  absWellDefined a b a=b | inl (inr a<0) | inl (inl 0<b) = exFalso (irreflexive {0G} (<Transitive 0<b (<WellDefined a=b (Equivalence.reflexive eq) a<0)))
  absWellDefined a b a=b | inl (inr a<0) | inl (inr b<0) = inverseWellDefined additiveGroup a=b
  absWellDefined a b a=b | inl (inr a<0) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq a=b (Equivalence.symmetric eq 0=b)) (Equivalence.reflexive eq) a<0))
  absWellDefined a b a=b | inr 0=a with totality 0R b
  absWellDefined a b a=b | inr 0=a | inl (inl 0<b) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (Equivalence.transitive eq 0=a a=b)) 0<b))
  absWellDefined a b a=b | inr 0=a | inl (inr b<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq 0=a a=b)) (Equivalence.reflexive eq) b<0))
  absWellDefined a b a=b | inr 0=a | inr 0=b = a=b

  lemm2 : (a : A) → a < 0G → 0G < inverse a
  lemm2 a a<0 with totality 0R (inverse a)
  lemm2 a a<0 | inl (inl 0<-a) = 0<-a
  lemm2 a a<0 | inl (inr -a<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder (<WellDefined (invLeft {a}) (identLeft {a}) (orderRespectsAddition -a<0 a)) a<0))
  lemm2 a a<0 | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq identRight) t) (Equivalence.reflexive eq) a<0))
    where
      t : a + 0G ∼ 0G
      t = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) 0=-a) (invRight {a})

  lemm2' : (a : A) → 0G < a → inverse a < 0G
  lemm2' a 0<a with totality 0R (inverse a)
  lemm2' a 0<a | inl (inl 0<-a) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<a (<WellDefined (identLeft {a}) (invLeft {a}) (orderRespectsAddition 0<-a a))))
  lemm2' a 0<a | inl (inr -a<0) = -a<0
  lemm2' a 0<a | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.symmetric eq identRight) t) 0<a))
    where
      t : a + 0G ∼ 0G
      t = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) 0=-a) (invRight {a})

  triangleInequality : (a b : A) → ((abs (a + b)) < ((abs a) + (abs b))) || (abs (a + b) ∼ (abs a) + (abs b))
  triangleInequality a b with totality 0R (a + b)
  triangleInequality a b | inl (inl 0<a+b) with totality 0R a
  triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) with totality 0R b
  triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) | inl (inl 0<b) = inr (Equivalence.reflexive eq)
  triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) | inl (inr b<0) = inl (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder b<0 (lemm2 b b<0)) a))
  triangleInequality a b | inl (inl 0<a+b) | inl (inl 0<a) | inr 0=b = inr (Equivalence.reflexive eq)
  triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) with totality 0R b
  triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) | inl (inl 0<b) = inl (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder a<0 (lemm2 a a<0)) b)
  triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) | inl (inr b<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<a+b (<WellDefined (Equivalence.reflexive eq) identLeft (ringAddInequalities a<0 b<0))))
  triangleInequality a b | inl (inl 0<a+b) | inl (inr a<0) | inr 0=b = inl (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder a<0 (lemm2 a a<0)) b)
  triangleInequality a b | inl (inl 0<a+b) | inr 0=a with totality 0R b
  triangleInequality a b | inl (inl 0<a+b) | inr 0=a | inl (inl 0<b) = inr (Equivalence.reflexive eq)
  triangleInequality a b | inl (inl 0<a+b) | inr 0=a | inl (inr b<0) = inl (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder b<0 (lemm2 b b<0)) a))
  triangleInequality a b | inl (inl 0<a+b) | inr 0=a | inr 0=b = inr (Equivalence.reflexive eq)
  triangleInequality a b | inl (inr a+b<0) with totality 0G a
  triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) with totality 0G b
  triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) | inl (inl 0<b) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities 0<a 0<b)) a+b<0))
  triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) | inl (inr b<0) = inl (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq (invContravariant additiveGroup)) (inverseWellDefined additiveGroup groupIsAbelian)) (Equivalence.reflexive eq) (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder (lemm2' _ 0<a) 0<a) (inverse b)))
  triangleInequality a b | inl (inr a+b<0) | inl (inl 0<a) | inr 0=b = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<a (<WellDefined (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) identRight) (Equivalence.reflexive eq) a+b<0)))
  triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) with totality 0G b
  triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) | inl (inl 0<b) = inl (<WellDefined (Equivalence.symmetric eq (invContravariant additiveGroup)) groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder (lemm2' _ 0<b) 0<b) (inverse a)))
  triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) | inl (inr b<0) = inr (Equivalence.transitive eq (invContravariant additiveGroup) groupIsAbelian)
  triangleInequality a b | inl (inr a+b<0) | inl (inr a<0) | inr 0=b = inr (Equivalence.transitive eq (invContravariant additiveGroup) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (+WellDefined (Equivalence.transitive eq (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=b)) (invIdent additiveGroup)) (Equivalence.reflexive eq)) identLeft) (Equivalence.symmetric eq identRight)) (+WellDefined (Equivalence.reflexive eq) 0=b)))
  triangleInequality a b | inl (inr a+b<0) | inr 0=a with totality 0G b
  triangleInequality a b | inl (inr a+b<0) | inr 0=a | inl (inl 0<b) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<b (<WellDefined (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.reflexive eq)) identLeft) (Equivalence.reflexive eq) a+b<0)))
  triangleInequality a b | inl (inr a+b<0) | inr 0=a | inl (inr b<0) = inr (Equivalence.transitive eq (invContravariant additiveGroup) (Equivalence.transitive eq groupIsAbelian (+WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq (inverseWellDefined additiveGroup 0=a)) (invIdent additiveGroup)) 0=a) (Equivalence.reflexive eq))))
  triangleInequality a b | inl (inr a+b<0) | inr 0=a | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.symmetric eq 0=b)) identLeft) (Equivalence.reflexive eq) a+b<0))
  triangleInequality a b | inr 0=a+b with totality 0G a
  triangleInequality a b | inr 0=a+b | inl (inl 0<a) with totality 0G b
  triangleInequality a b | inr 0=a+b | inl (inl 0<a) | inl (inl 0<b) = exFalso (irreflexive {0G} (<WellDefined identLeft (Equivalence.symmetric eq 0=a+b) (ringAddInequalities 0<a 0<b)))
  triangleInequality a b | inr 0=a+b | inl (inl 0<a) | inl (inr b<0) = inl (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder b<0 (lemm2 _ b<0)) a))
  triangleInequality a b | inr 0=a+b | inl (inl 0<a) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (lemm3 _ _ (Equivalence.transitive eq 0=a+b groupIsAbelian) 0=b)) 0<a))
  triangleInequality a b | inr 0=a+b | inl (inr a<0) with totality 0G b
  triangleInequality a b | inr 0=a+b | inl (inr a<0) | inl (inl 0<b) = inl (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder a<0 (lemm2 _ a<0)) b)
  triangleInequality a b | inr 0=a+b | inl (inr a<0) | inl (inr b<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq 0=a+b) identLeft (ringAddInequalities a<0 b<0)))
  triangleInequality a b | inr 0=a+b | inl (inr a<0) | inr 0=b = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (lemm3 _ _ (Equivalence.transitive eq 0=a+b groupIsAbelian) 0=b)) (Equivalence.reflexive eq) a<0))
  triangleInequality a b | inr 0=a+b | inr 0=a with totality 0G b
  triangleInequality a b | inr 0=a+b | inr 0=a | inl (inl 0<b) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (lemm3 a b 0=a+b 0=a)) 0<b))
  triangleInequality a b | inr 0=a+b | inr 0=a | inl (inr b<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (lemm3 a b 0=a+b 0=a)) (Equivalence.reflexive eq) b<0))
  triangleInequality a b | inr 0=a+b | inr 0=a | inr 0=b = inr (Equivalence.reflexive eq)

  ringMinusFlipsOrder : {x : A} → (Ring.0R R) < x → (Group.inverse (Ring.additiveGroup R) x) < (Ring.0R R)
  ringMinusFlipsOrder {x = x} 0<x with totality (Ring.0R R) (Group.inverse (Ring.additiveGroup R) x)
  ringMinusFlipsOrder {x} 0<x | inl (inl 0<inv) = exFalso (SetoidPartialOrder.irreflexive pOrder bad')
    where
    bad : (Group.0G (Ring.additiveGroup R) + Group.0G (Ring.additiveGroup R)) < (x + Group.inverse (Ring.additiveGroup R) x)
    bad = ringAddInequalities 0<x 0<inv
    bad' : (Group.0G (Ring.additiveGroup R)) < (Group.0G (Ring.additiveGroup R))
    bad' = SetoidPartialOrder.<WellDefined pOrder (Group.identRight (Ring.additiveGroup R)) (Group.invRight (Ring.additiveGroup R)) bad
  ringMinusFlipsOrder {x} 0<x | inl (inr inv<0) = inv<0
  ringMinusFlipsOrder {x} 0<x | inr 0=inv = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (Equivalence.reflexive (Setoid.eq S)) (groupLemmaMove0G (Ring.additiveGroup R) 0=inv) 0<x))

  ringMinusFlipsOrder' : {x : A} → (Group.inverse (Ring.additiveGroup R) x) < (Ring.0R R) → (Ring.0R R) < x
  ringMinusFlipsOrder' {x} -x<0 with totality (Ring.0R R) x
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

  ringCanCancelPositive : {x y c : A} → (Ring.0R R) < c → (x * c) < (y * c) → x < y
  ringCanCancelPositive {x} {y} {c} 0<c xc<yc = SetoidPartialOrder.<WellDefined pOrder (Group.identLeft additiveGroup) (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive (Group.invLeft additiveGroup)) (Group.identRight additiveGroup))) q''
    where
      open Equivalence (Setoid.eq S)
      have : 0R < ((y * c) + (Group.inverse additiveGroup (x * c)))
      have = SetoidPartialOrder.<WellDefined pOrder (Group.invRight additiveGroup) reflexive (orderRespectsAddition xc<yc (Group.inverse additiveGroup _))
      p1 : 0R < ((y * c) + ((Group.inverse additiveGroup x) * c))
      p1 = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (symmetric (Equivalence.transitive eq (*Commutative) (Equivalence.transitive eq ringMinusExtracts (inverseWellDefined additiveGroup *Commutative))))) have
      q : 0R < ((y + Group.inverse additiveGroup x) * c)
      q = SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq (Equivalence.transitive eq (Group.+WellDefined additiveGroup *Commutative *Commutative) (symmetric *DistributesOver+)) *Commutative) p1
      q' : 0R < (y + Group.inverse additiveGroup x)
      q' with totality 0R (y + Group.inverse additiveGroup x)
      q' | inl (inl pr) = pr
      q' | inl (inr y-x<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq *Commutative (Ring.timesZero R)) k))
        where
          f : ((y + inverse x) + (inverse (y + inverse x))) < (0G + inverse (y + inverse x))
          f = orderRespectsAddition y-x<0 _
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
          g = Equivalence.transitive eq (symmetric (invIdent additiveGroup)) (Equivalence.transitive eq f (Equivalence.transitive eq (Equivalence.transitive eq (invContravariant additiveGroup) groupIsAbelian) (+WellDefined reflexive (invInv additiveGroup))))
          x=y : x ∼ y
          x=y = transferToRight additiveGroup (symmetric (Equivalence.transitive eq g groupIsAbelian))
      q'' : (0R + x) < ((y + Group.inverse additiveGroup x) + x)
      q'' = orderRespectsAddition q' x


  ringCanCancelNegative : {x y c : A} → c < (Ring.0R R) → (x * c) < (y * c) → y < x
  ringCanCancelNegative {x} {y} {c} c<0 xc<yc = r
    where
      open Equivalence eq
      p0 : 0R < ((y * c) + inverse (x * c))
      p0 = SetoidPartialOrder.<WellDefined pOrder invRight reflexive (orderRespectsAddition xc<yc (inverse (x * c)))
      p1 : 0R < ((y * c) + ((inverse x) * c))
      p1 = SetoidPartialOrder.<WellDefined pOrder reflexive (Group.+WellDefined additiveGroup reflexive (Equivalence.transitive eq (inverseWellDefined additiveGroup *Commutative) (Equivalence.transitive eq (symmetric ringMinusExtracts) *Commutative))) p0
      p2 : 0R < ((y + inverse x) * c)
      p2 = SetoidPartialOrder.<WellDefined pOrder reflexive (Equivalence.transitive eq (Group.+WellDefined additiveGroup *Commutative *Commutative) (Equivalence.transitive eq (symmetric *DistributesOver+) *Commutative)) p1
      q : (y + inverse x) < 0R
      q with totality 0R (y + inverse x)
      q | inl (inl pr) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<Transitive pOrder bad c<0))
        where
          bad : 0R < c
          bad = ringCanCancelPositive pr (SetoidPartialOrder.<WellDefined pOrder (symmetric (Equivalence.transitive eq *Commutative (Ring.timesZero R))) *Commutative p2)
      q | inl (inr pr) = pr
      q | inr 0=y-x = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (*WellDefined x=y reflexive) reflexive xc<yc))
        where
          x=y : x ∼ y
          x=y = Equivalence.transitive eq (symmetric identLeft) (Equivalence.transitive eq (Group.+WellDefined additiveGroup 0=y-x reflexive) (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive invLeft) identRight)))
      r : y < x
      r = SetoidPartialOrder.<WellDefined pOrder (Equivalence.transitive eq (symmetric (Group.+Associative additiveGroup)) (Equivalence.transitive eq (Group.+WellDefined additiveGroup reflexive (invLeft)) identRight)) (Group.identLeft additiveGroup) (orderRespectsAddition q x)

  absZero : abs (Ring.0R R) ≡ Ring.0R R
  absZero with totality (Ring.0R R) (Ring.0R R)
  absZero | inl (inl x) = exFalso (irreflexive x)
  absZero | inl (inr x) = exFalso (irreflexive x)
  absZero | inr x = refl

  absNegation : (a : A) → (abs a) ∼ (abs (inverse a))
  absNegation a with totality 0R a
  absNegation a | inl (inl 0<a) with totality 0G (inverse a)
  absNegation a | inl (inl 0<a) | inl (inl 0<-a) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<-a (lemm2' a 0<a)))
  absNegation a | inl (inl 0<a) | inl (inr -a<0) = Equivalence.symmetric eq (invTwice additiveGroup a)
  absNegation a | inl (inl 0<a) | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq (invTwice additiveGroup a)) (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=-a))) (invIdent additiveGroup)) 0<a))
  absNegation a | inl (inr a<0) with totality 0G (inverse a)
  absNegation a | inl (inr a<0) | inl (inl 0<-a) = Equivalence.reflexive eq
  absNegation a | inl (inr a<0) | inl (inr -a<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder (<WellDefined (Equivalence.reflexive eq) (invTwice additiveGroup a) (lemm2 (inverse a) -a<0)) a<0))
  absNegation a | inl (inr a<0) | inr 0=-a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq (Equivalence.transitive eq (inverseWellDefined additiveGroup 0=-a) (invTwice additiveGroup a))) (invIdent additiveGroup)) (Equivalence.reflexive eq) a<0))
  absNegation a | inr 0=a with totality 0G (inverse a)
  absNegation a | inr 0=a | inl (inl 0<-a) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=a)) (invIdent additiveGroup)) 0<-a))
  absNegation a | inr 0=a | inl (inr -a<0) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.transitive eq (inverseWellDefined additiveGroup (Equivalence.symmetric eq 0=a)) (invIdent additiveGroup)) (Equivalence.reflexive eq) -a<0))
  absNegation a | inr 0=a | inr 0=-a = Equivalence.transitive eq (Equivalence.symmetric eq 0=a) 0=-a

  posTimesNeg : (a b : A) → (0G < a) → (b < 0G) → (a * b) < 0G
  posTimesNeg a b 0<a b<0 with orderRespectsMultiplication 0<a (lemm2 _ b<0)
  ... | bl = <WellDefined (invTwice additiveGroup _) (Equivalence.reflexive eq) (lemm2' _ (<WellDefined (Equivalence.reflexive eq) ringMinusExtracts bl))

  negTimesPos : (a b : A) → (a < 0G) → (b < 0G) → 0G < (a * b)
  negTimesPos a b a<0 b<0 with orderRespectsMultiplication (lemm2 _ a<0) (lemm2 _ b<0)
  ... | bl = <WellDefined (Equivalence.reflexive eq) twoNegativesTimes bl

  absRespectsTimes : (a b : A) → abs (a * b) ∼ (abs a) * (abs b)
  absRespectsTimes a b with totality 0R a
  absRespectsTimes a b | inl (inl 0<a) with totality 0R b
  absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) with totality 0R (a * b)
  absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) | inl (inl 0<ab) = Equivalence.reflexive eq
  absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) | inl (inr ab<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder (orderRespectsMultiplication 0<a 0<b) ab<0))
  absRespectsTimes a b | inl (inl 0<a) | inl (inl 0<b) | inr 0=ab = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=ab) (orderRespectsMultiplication 0<a 0<b)))
  absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) with totality 0R (a * b)
  absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) | inl (inl 0<ab) with <WellDefined (Equivalence.reflexive eq) ringMinusExtracts (orderRespectsMultiplication 0<a (lemm2 b b<0))
  ... | bl = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<ab (<WellDefined (invTwice additiveGroup _) (Equivalence.reflexive eq) (lemm2' _ bl))))
  absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) | inl (inr ab<0) = Equivalence.symmetric eq ringMinusExtracts
  absRespectsTimes a b | inl (inl 0<a) | inl (inr b<0) | inr 0=ab = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq 0=ab) (Equivalence.reflexive eq) (posTimesNeg a b 0<a b<0)))
  absRespectsTimes a b | inl (inl 0<a) | inr 0=b with totality 0R (a * b)
  absRespectsTimes a b | inl (inl 0<a) | inr 0=b | inl (inl 0<ab) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) (timesZero {a})) 0<ab))
  absRespectsTimes a b | inl (inl 0<a) | inr 0=b | inl (inr ab<0) = exFalso ((irreflexive {0G} (<WellDefined (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=b)) (timesZero {a})) (Equivalence.reflexive eq) ab<0)))
  absRespectsTimes a b | inl (inl 0<a) | inr 0=b | inr 0=ab = Equivalence.reflexive eq
  absRespectsTimes a b | inl (inr a<0) with totality 0R b
  absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) with totality 0R (a * b)
  absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) | inl (inl 0<ab) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<ab (<WellDefined *Commutative (Equivalence.reflexive eq) (posTimesNeg b a 0<b a<0))))
  absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) | inl (inr ab<0) = Equivalence.symmetric eq ringMinusExtracts'
  absRespectsTimes a b | inl (inr a<0) | inl (inl 0<b) | inr 0=ab = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq 0=ab *Commutative)) (Equivalence.reflexive eq) (posTimesNeg b a 0<b a<0)))
  absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) with totality 0R (a * b)
  absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) | inl (inl 0<ab) = Equivalence.symmetric eq twoNegativesTimes
  absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) | inl (inr ab<0) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder (negTimesPos a b a<0 b<0) ab<0))
  absRespectsTimes a b | inl (inr a<0) | inl (inr b<0) | inr 0=ab = exFalso (exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=ab) (negTimesPos a b a<0 b<0))))
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

  absNonnegative : {a : A} → (abs a < 0R) → False
  absNonnegative {a} pr with totality 0R a
  absNonnegative {a} pr | inl (inl x) = irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder x pr)
  absNonnegative {a} pr | inl (inr x) = irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder (<WellDefined (Equivalence.reflexive eq) (invTwice additiveGroup a) (lemm2 (inverse a) pr)) x)
  absNonnegative {a} pr | inr x = irreflexive {0G} (<WellDefined (Equivalence.symmetric eq x) (Equivalence.reflexive eq) pr)

  a-bPos : {a b : A} → ((a ∼ b) → False) → 0R < abs (a + inverse b)
  a-bPos {a} {b} a!=b with totality 0R (a + inverse b)
  a-bPos {a} {b} a!=b | inl (inl x) = x
  a-bPos {a} {b} a!=b | inl (inr x) = lemm2 _ x
  a-bPos {a} {b} a!=b | inr x = exFalso (a!=b (transferToRight additiveGroup (Equivalence.symmetric eq x)))

  absZeroImpliesZero : {a : A} → abs a ∼ 0R → a ∼ 0R
  absZeroImpliesZero {a} a=0 with totality 0R a
  absZeroImpliesZero {a} a=0 | inl (inl 0<a) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) a=0 0<a))
  absZeroImpliesZero {a} a=0 | inl (inr a<0) = Equivalence.symmetric eq (lemm3 (inverse a) a (Equivalence.symmetric eq invLeft) (Equivalence.symmetric eq a=0))
  absZeroImpliesZero {a} a=0 | inr 0=a = a=0

  halvePositive : (a : A) → 0R < (a + a) → 0R < a
  halvePositive a 0<2a with totality 0R a
  halvePositive a 0<2a | inl (inl x) = x
  halvePositive a 0<2a | inl (inr a<0) = exFalso (irreflexive {a + a} (SetoidPartialOrder.<Transitive pOrder (<WellDefined (Equivalence.reflexive eq) identRight (ringAddInequalities a<0 a<0)) 0<2a))
  halvePositive a 0<2a | inr x = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq x) (Equivalence.symmetric eq x)) identRight) 0<2a))

  halvePositive' : {a b : A} → (a + a) ∼ b → 0R < b → 0R < a
  halvePositive' {a} {b} pr 0<b = halvePositive a (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr) 0<b)

  0<1 : (0R ∼ 1R → False) → 0R < 1R
  0<1 0!=1 with totality 0R 1R
  0<1 0!=1 | inl (inl x) = x
  0<1 0!=1 | inl (inr x) = <WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq twoNegativesTimes identIsIdent) (orderRespectsMultiplication (lemm2 1R x) (lemm2 1R x))
  0<1 0!=1 | inr x = exFalso (0!=1 x)

  addingAbsCannotShrink : {a b : A} → 0G < b → 0G < ((abs a) + b)
  addingAbsCannotShrink {a} {b} 0<b with totality 0G a
  addingAbsCannotShrink {a} {b} 0<b | inl (inl x) = <WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities x 0<b)
  addingAbsCannotShrink {a} {b} 0<b | inl (inr x) = <WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities (lemm2 a x) 0<b)
  addingAbsCannotShrink {a} {b} 0<b | inr x = <WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.symmetric eq identLeft) (+WellDefined x (Equivalence.reflexive eq))) 0<b

  1<0False : (1R < 0R) → False
  1<0False 1<0 with orderRespectsMultiplication (lemm2 _ 1<0) (lemm2 _ 1<0)
  ... | bl = exFalso (irreflexive (SetoidPartialOrder.<Transitive pOrder 1<0 (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (twoNegativesTimes) identIsIdent) bl)))

  greaterZeroImpliesEqualAbs : {a : A} → 0R < a → a ∼ abs a
  greaterZeroImpliesEqualAbs {a} 0<a with totality 0R a
  ... | inl (inl _) = Equivalence.reflexive eq
  ... | inl (inr a<0) = exFalso (irreflexive (SetoidPartialOrder.<Transitive pOrder a<0 0<a))
  ... | inr 0=a = exFalso (irreflexive (<WellDefined 0=a (Equivalence.reflexive eq) 0<a))

  lessZeroImpliesEqualNegAbs : {a : A} → a < 0R → abs a ∼ inverse a
  lessZeroImpliesEqualNegAbs {a} a<0 with totality 0R a
  ... | inl (inr _) = Equivalence.reflexive eq
  ... | inl (inl 0<a) = exFalso (irreflexive (SetoidPartialOrder.<Transitive pOrder a<0 0<a))
  ... | inr 0=a = exFalso (irreflexive (<WellDefined (Equivalence.reflexive eq) 0=a a<0))

  absZeroIsZero : abs 0R ∼ 0R
  absZeroIsZero with totality 0R 0R
  ... | inl (inl bad) = exFalso (irreflexive bad)
  ... | inl (inr bad) = exFalso (irreflexive bad)
  ... | inr _ = Equivalence.reflexive eq

  greaterThanAbsImpliesGreaterThan0 : {a b : A} → (abs a) < b → 0R < b
  greaterThanAbsImpliesGreaterThan0 {a} {b} a<b with totality 0R a
  greaterThanAbsImpliesGreaterThan0 {a} {b} a<b | inl (inl 0<a) = SetoidPartialOrder.<Transitive pOrder 0<a a<b
  greaterThanAbsImpliesGreaterThan0 {a} {b} a<b | inl (inr a<0) = SetoidPartialOrder.<Transitive pOrder (lemm2 _ a<0) a<b
  greaterThanAbsImpliesGreaterThan0 {a} {b} a<b | inr 0=a = <WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.reflexive eq) a<b

  abs1Is1 : abs 1R ∼ 1R
  abs1Is1 with totality 0R 1R
  abs1Is1 | inl (inl 0<1) = Equivalence.reflexive eq
  abs1Is1 | inl (inr 1<0) = exFalso (1<0False 1<0)
  abs1Is1 | inr 0=1 = Equivalence.reflexive eq

  absBoundedImpliesBounded : {a b : A} → abs a < b → a < b
  absBoundedImpliesBounded {a} {b} a<b with totality 0G a
  absBoundedImpliesBounded {a} {b} a<b | inl (inl x) = a<b
  absBoundedImpliesBounded {a} {b} a<b | inl (inr x) = SetoidPartialOrder.<Transitive pOrder x (SetoidPartialOrder.<Transitive pOrder (lemm2 a x) a<b)
  absBoundedImpliesBounded {a} {b} a<b | inr x = a<b

  orderedImpliesCharNot2 : (0R ∼ 1R → False) → 1R + 1R ∼ 0R → False
  orderedImpliesCharNot2 0!=1 x = irreflexive (<WellDefined (identRight {0R}) x (ringAddInequalities (0<1 0!=1) (0<1 0!=1)))

open import Rings.InitialRing R
open Equivalence eq

fromNIncreasing : (0R ∼ 1R → False) → (n : ℕ) → (fromN n) < (fromN (succ n))
fromNIncreasing 0!=1 zero = <WellDefined reflexive (symmetric identRight) (0<1 0!=1)
fromNIncreasing 0!=1 (succ n) = <WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (fromNIncreasing 0!=1 n) 1R)

fromNPreservesOrder : (0R ∼ 1R → False) → {a b : ℕ} → (a <N b) → (fromN a) < (fromN b)
fromNPreservesOrder 0!=1 {zero} {succ zero} a<b = fromNIncreasing 0!=1 0
fromNPreservesOrder 0!=1 {zero} {succ (succ b)} a<b = <Transitive (fromNPreservesOrder 0!=1 (succIsPositive b)) (fromNIncreasing 0!=1 (succ b))
fromNPreservesOrder 0!=1 {succ a} {succ b} a<b = <WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (fromNPreservesOrder 0!=1 (canRemoveSuccFrom<N a<b)) 1R)

reciprocalPositive : (a b : A) → .(0<a : 0R < a) → (a * b ∼ 1R) → 0R < b
reciprocalPositive a 1/a 0<a ab=1 with totality 0G 1/a
... | inl (inl x) = x
... | inl (inr x) = exFalso (1<0False (<WellDefined (transitive *Commutative ab=1) timesZero' (ringCanMultiplyByPositive 0<a x)))
... | inr x = exFalso (anyComparisonImpliesNontrivial 0<a (transitive (transitive (symmetric timesZero) (*WellDefined reflexive x)) ab=1))

reciprocal<1 : (a b : A) → .(1<a : 1R < a) → (a * b ∼ 1R) → b < 1R
reciprocal<1 a b 0<a ab=1 with totality b 1R
... | inl (inl x) = x
... | inr b=1 = exFalso (irreflexive (<WellDefined (symmetric ab=1) (transitive (symmetric identIsIdent) (transitive *Commutative ((*WellDefined reflexive (symmetric b=1))))) 0<a))
... | inl (inr x) = exFalso (irreflexive (<WellDefined identIsIdent ab=1 (ringMultiplyPositives (0<1 (anyComparisonImpliesNontrivial 0<a)) (0<1 (anyComparisonImpliesNontrivial 0<a)) 0<a x)))
