{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Setoids.Setoids
open import Functions.Definition
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Orders.Total.Definition
open import Rings.IntegralDomains.Definition

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

abstract

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

  posTimesNeg : (a b : A) → (0G < a) → (b < 0G) → (a * b) < 0G
  posTimesNeg a b 0<a b<0 with orderRespectsMultiplication 0<a (lemm2 _ b<0)
  ... | bl = <WellDefined (invTwice additiveGroup _) (Equivalence.reflexive eq) (lemm2' _ (<WellDefined (Equivalence.reflexive eq) ringMinusExtracts bl))

  negTimesPos : (a b : A) → (a < 0G) → (b < 0G) → 0G < (a * b)
  negTimesPos a b a<0 b<0 with orderRespectsMultiplication (lemm2 _ a<0) (lemm2 _ b<0)
  ... | bl = <WellDefined (Equivalence.reflexive eq) twoNegativesTimes bl

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


  1<0False : (1R < 0R) → False
  1<0False 1<0 with orderRespectsMultiplication (lemm2 _ 1<0) (lemm2 _ 1<0)
  ... | bl = exFalso (irreflexive (SetoidPartialOrder.<Transitive pOrder 1<0 (<WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (twoNegativesTimes) identIsIdent) bl)))

  orderedImpliesCharNot2 : (0R ∼ 1R → False) → 1R + 1R ∼ 0R → False
  orderedImpliesCharNot2 0!=1 x = irreflexive (<WellDefined (identRight {0R}) x (ringAddInequalities (0<1 0!=1) (0<1 0!=1)))

open import Rings.InitialRing R
open Equivalence eq

fromNPreservesOrder' : (0R ∼ 1R → False) → {a b : ℕ} → (fromN a) < (fromN b) → a <N b
fromNPreservesOrder' nontrivial {a} {b} a<b with TotalOrder.totality ℕTotalOrder a b
... | inl (inl x) = x
... | inl (inr x) = exFalso (irreflexive (<Transitive a<b (fromNPreservesOrder (0<1 nontrivial) x)))
... | inr x = exFalso (irreflexive (<WellDefined (fromNWellDefined x) reflexive a<b))

reciprocalPositive : (a b : A) → .(0<a : 0R < a) → (a * b ∼ 1R) → 0R < b
reciprocalPositive a 1/a 0<a ab=1 with totality 0G 1/a
... | inl (inl x) = x
... | inl (inr x) = exFalso (1<0False (<WellDefined (transitive *Commutative ab=1) timesZero' (ringCanMultiplyByPositive 0<a x)))
... | inr x = exFalso (anyComparisonImpliesNontrivial 0<a (transitive (transitive (symmetric timesZero) (*WellDefined reflexive x)) ab=1))

reciprocalPositive' : (a b : A) → .(0<a : 0R < a) → (b * a ∼ 1R) → 0R < b
reciprocalPositive' a 1/a 0<a ab=1 = reciprocalPositive a 1/a 0<a (transitive *Commutative ab=1)

reciprocal<1 : (a b : A) → .(1<a : 1R < a) → (a * b ∼ 1R) → b < 1R
reciprocal<1 a b 0<a ab=1 with totality b 1R
... | inl (inl x) = x
... | inr b=1 = exFalso (irreflexive (<WellDefined (symmetric ab=1) (transitive (symmetric identIsIdent) (transitive *Commutative ((*WellDefined reflexive (symmetric b=1))))) 0<a))
... | inl (inr x) = exFalso (irreflexive (<WellDefined identIsIdent ab=1 (ringMultiplyPositives (0<1 (anyComparisonImpliesNontrivial 0<a)) (0<1 (anyComparisonImpliesNontrivial 0<a)) 0<a x)))

isIntDom : (nonempty : 1R ∼ 0R → False) → IntegralDomain R
IntegralDomain.intDom (isIntDom n) {a} {b} ab=0 a!=0 with totality 0R b
... | inr 0=b = symmetric 0=b
IntegralDomain.intDom (isIntDom n) {a} {b} ab=0 a!=0 | inl (inl 0<b) with totality 0R a
... | inl (inl x) = exFalso (irreflexive (<WellDefined reflexive ab=0 (orderRespectsMultiplication x 0<b)))
... | inl (inr x) = exFalso (irreflexive (<WellDefined ab=0 timesZero' (ringCanMultiplyByPositive 0<b x)))
... | inr x = exFalso (a!=0 (symmetric x))
IntegralDomain.intDom (isIntDom n) {a} {b} ab=0 a!=0 | inl (inr b<0) with totality 0R a
... | inl (inl x) = exFalso (irreflexive (<WellDefined (transitive *Commutative ab=0) timesZero' (ringCanMultiplyByPositive x b<0)))
... | inl (inr x) = exFalso (irreflexive (<WellDefined reflexive (transitive twoNegativesTimes ab=0) (orderRespectsMultiplication (lemm2 a x) (lemm2 b b<0))))
... | inr x = exFalso (a!=0 (symmetric x))
IntegralDomain.nontrivial (isIntDom n) = n
