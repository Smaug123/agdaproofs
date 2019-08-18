{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Groups.Groups
open import Groups.GroupDefinition
open import Groups.GroupsLemmas
open import Rings.Definition
open import Setoids.Setoids
open import Setoids.Orders

module Rings.Lemmas where
  ringTimesZero : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) → {x : A} → Setoid._∼_ S (x * (Ring.0R R)) (Ring.0R R)
  ringTimesZero {S = S} {_+_ = _+_} {_*_ = _*_} R {x} = symmetric (transitive blah'' (transitive (Group.multAssoc additiveGroup) (transitive (wellDefined invLeft reflexive) multIdentLeft)))
    where
      open Ring R
      open Group additiveGroup
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      blah : (x * 0R) ∼ (x * 0R) + (x * 0R)
      blah = transitive (multWellDefined reflexive (symmetric multIdentRight)) multDistributes
      blah' : (inverse (x * 0R)) + (x * 0R) ∼ (inverse (x * 0R)) + ((x * 0R) + (x * 0R))
      blah' = wellDefined reflexive blah
      blah'' : 0R ∼ (inverse (x * 0R)) + ((x * 0R) + (x * 0R))
      blah'' = transitive (symmetric invLeft) blah'

  ringMinusExtracts : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) → {x y : A} → Setoid._∼_ S (x * Group.inverse (Ring.additiveGroup R) y) (Group.inverse (Ring.additiveGroup R) (x * y))
  ringMinusExtracts {S = S} {_+_ = _+_} {_*_ = _*_} R {x = x} {y} = transferToRight' additiveGroup (transitive (symmetric multDistributes) (transitive (multWellDefined reflexive invLeft) (ringTimesZero R)))
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Ring R
      open Group additiveGroup

  ringAddInequalities : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {w x y z : A} → w < x → y < z → (w + y) < (x + z)
  ringAddInequalities {S = S} {_+_ = _+_} {R = R} {_<_ = _<_} {pOrder = pOrder} oRing {w = w} {x} {y} {z} w<x y<z = transitive (orderRespectsAddition w<x y) (wellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition y<z x))
    where
      open SetoidPartialOrder pOrder
      open OrderedRing oRing
      open Ring R

  groupLemmaMoveIdentity : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → (Setoid._∼_ S (Group.identity G) (Group.inverse G x)) → Setoid._∼_ S x (Group.identity G)
  groupLemmaMoveIdentity {S = S} G {x} pr = transitive (symmetric (invInv G)) (transitive (symmetric p) (invIdent G))
    where
      open Group G
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      p : inverse identity ∼ inverse (inverse x)
      p = inverseWellDefined G pr

  groupLemmaMoveIdentity' : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → Setoid._∼_ S x (Group.identity G) → (Setoid._∼_ S (Group.identity G) (Group.inverse G x))
  groupLemmaMoveIdentity' {S = S} G {x} pr = transferToRight' G (transitive multIdentLeft pr)
    where
      open Group G
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  ringMinusFlipsOrder : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x : A} → (Ring.0R R) < x → (Group.inverse (Ring.additiveGroup R) x) < (Ring.0R R)
  ringMinusFlipsOrder {S = S} {_+_ = _+_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} oRing {x = x} 0<x with SetoidTotalOrder.totality tOrder (Ring.0R R) (Group.inverse (Ring.additiveGroup R) x)
  ringMinusFlipsOrder {S = S} {_+_} {R = R} {_<_} {pOrder} {tOrder} oRing {x} 0<x | inl (inl 0<inv) = exFalso (SetoidPartialOrder.irreflexive pOrder bad')
    where
      bad : (Group.identity (Ring.additiveGroup R) + Group.identity (Ring.additiveGroup R)) < (x + Group.inverse (Ring.additiveGroup R) x)
      bad = ringAddInequalities oRing 0<x 0<inv
      bad' : (Group.identity (Ring.additiveGroup R)) < (Group.identity (Ring.additiveGroup R))
      bad' = SetoidPartialOrder.wellDefined pOrder (Group.multIdentRight (Ring.additiveGroup R)) (Group.invRight (Ring.additiveGroup R)) bad
  ringMinusFlipsOrder {S = S} {_+_} {R = R} {_<_} {pOrder} {tOrder} oRing {x} 0<x | inl (inr inv<0) = inv<0
  ringMinusFlipsOrder {S = S} {_+_} {R = R} {_<_} {pOrder} {tOrder} oRing {x} 0<x | inr 0=inv = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (groupLemmaMoveIdentity (Ring.additiveGroup R) 0=inv) 0<x))

  ringMinusFlipsOrder' : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x : A} → (Group.inverse (Ring.additiveGroup R) x) < (Ring.0R R) → (Ring.0R R) < x
  ringMinusFlipsOrder' {R = R} {_<_ = _<_} {tOrder = tOrder} oRing {x} -x<0 with SetoidTotalOrder.totality tOrder (Ring.0R R) x
  ringMinusFlipsOrder' {R = R} {_<_} {tOrder = tOrder} oRing {x} -x<0 | inl (inl 0<x) = 0<x
  ringMinusFlipsOrder' {_+_ = _+_} {R = R} {_<_} {pOrder = pOrder} {tOrder = tOrder} oRing {x} -x<0 | inl (inr x<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder (Group.invLeft (Ring.additiveGroup R)) (Group.multIdentRight (Ring.additiveGroup R)) bad))
    where
      bad : ((Group.inverse (Ring.additiveGroup R) x) + x) < (Group.identity (Ring.additiveGroup R) + Group.identity (Ring.additiveGroup R))
      bad = ringAddInequalities oRing -x<0 x<0
  ringMinusFlipsOrder' {S = S} {R = R} {_<_} {pOrder = pOrder} {tOrder = tOrder} oRing {x} -x<0 | inr 0=x = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder (symmetric (groupLemmaMoveIdentity' (Ring.additiveGroup R) (symmetric 0=x))) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) -x<0))
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  ringMinusFlipsOrder'' : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x : A} → x < (Ring.0R R) → (Ring.0R R) < Group.inverse (Ring.additiveGroup R) x
  ringMinusFlipsOrder'' {S = S} {R = R} {pOrder = pOrder} oRing {x} x<0 = ringMinusFlipsOrder' oRing (SetoidPartialOrder.wellDefined pOrder {x} {Group.inverse (Ring.additiveGroup R) (Group.inverse (Ring.additiveGroup R) x)} {Ring.0R R} {Ring.0R R} (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (invInv (Ring.additiveGroup R))) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) x<0)

  ringMinusFlipsOrder''' : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x : A} → (Ring.0R R) < (Group.inverse (Ring.additiveGroup R) x) → x < (Ring.0R R)
  ringMinusFlipsOrder''' {S = S} {R = R} {pOrder = pOrder} oRing {x} 0<-x = SetoidPartialOrder.wellDefined pOrder (invInv (Ring.additiveGroup R)) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (ringMinusFlipsOrder oRing 0<-x)

  ringCanMultiplyByPositive : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x y c : A} → (Ring.0R R) < c → x < y → (x * c) < (y * c)
  ringCanMultiplyByPositive {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} oRing {x} {y} {c} 0<c x<y = SetoidPartialOrder.wellDefined pOrder reflexive (Group.multIdentRight additiveGroup) q'
    where
      open Ring R
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      have : 0R < (y + Group.inverse additiveGroup x)
      have = SetoidPartialOrder.wellDefined pOrder (Group.invRight additiveGroup) reflexive (OrderedRing.orderRespectsAddition oRing x<y (Group.inverse additiveGroup x))
      p : 0R < ((y * c) + ((Group.inverse additiveGroup x) * c))
      p = SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (transitive multDistributes ((Group.wellDefined additiveGroup) multCommutative multCommutative))) (OrderedRing.orderRespectsMultiplication oRing have 0<c)
      p' : 0R < ((y * c) + (Group.inverse additiveGroup (x * c)))
      p' = SetoidPartialOrder.wellDefined pOrder reflexive (Group.wellDefined additiveGroup reflexive (transitive (transitive multCommutative (ringMinusExtracts R)) (inverseWellDefined additiveGroup multCommutative))) p
      q : (0R + (x * c)) < (((y * c) + (Group.inverse additiveGroup (x * c))) + (x * c))
      q = OrderedRing.orderRespectsAddition oRing p' (x * c)
      q' : (x * c) < ((y * c) + 0R)
      q' = SetoidPartialOrder.wellDefined pOrder (Group.multIdentLeft additiveGroup) (transitive (symmetric (Group.multAssoc additiveGroup)) (Group.wellDefined additiveGroup reflexive (Group.invLeft additiveGroup))) q

  ringCanCancelPositive : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x y c : A} → (Ring.0R R) < c → (x * c) < (y * c) → x < y
  ringCanCancelPositive {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} oRing {x} {y} {c} 0<c xc<yc = SetoidPartialOrder.wellDefined pOrder (Group.multIdentLeft additiveGroup) (transitive (symmetric (Group.multAssoc additiveGroup)) (transitive (Group.wellDefined additiveGroup reflexive (Group.invLeft additiveGroup)) (Group.multIdentRight additiveGroup))) q''
    where
      open Ring R
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      have : 0R < ((y * c) + (Group.inverse additiveGroup (x * c)))
      have = SetoidPartialOrder.wellDefined pOrder (Group.invRight additiveGroup) reflexive (OrderedRing.orderRespectsAddition oRing xc<yc (Group.inverse additiveGroup _))
      p : 0R < ((y * c) + ((Group.inverse additiveGroup x) * c))
      p = SetoidPartialOrder.wellDefined pOrder reflexive (Group.wellDefined additiveGroup reflexive (symmetric (transitive (multCommutative) (transitive (ringMinusExtracts R) (inverseWellDefined additiveGroup multCommutative))))) have
      q : 0R < ((y + Group.inverse additiveGroup x) * c)
      q = SetoidPartialOrder.wellDefined pOrder reflexive (transitive (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (symmetric multDistributes)) multCommutative) p
      q' : 0R < (y + Group.inverse additiveGroup x)
      q' with SetoidTotalOrder.totality tOrder 0R (y + Group.inverse additiveGroup x)
      q' | inl (inl pr) = pr
      q' | inl (inr y-x<0) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder reflexive (transitive multCommutative (ringTimesZero R)) k))
        where
          open Group additiveGroup
          f : ((y + inverse x) + (inverse (y + inverse x))) < (identity + inverse (y + inverse x))
          f = OrderedRing.orderRespectsAddition oRing y-x<0 _
          g : identity < inverse (y + inverse x)
          g = SetoidPartialOrder.wellDefined pOrder invRight multIdentLeft f
          h : (identity * c) < ((inverse (y + inverse x)) * c)
          h = ringCanMultiplyByPositive oRing 0<c g
          i : (0R + (identity * c)) < (((y + inverse x) * c) + ((inverse (y + inverse x)) * c))
          i = ringAddInequalities oRing q h
          j : 0R < (((y + inverse x) + (inverse (y + inverse x))) * c)
          j = SetoidPartialOrder.wellDefined pOrder (transitive multIdentLeft (transitive multCommutative (ringTimesZero R))) (symmetric (transitive multCommutative (transitive multDistributes (Group.wellDefined additiveGroup multCommutative multCommutative)))) i
          k : 0R < (0R * c)
          k = SetoidPartialOrder.wellDefined pOrder reflexive (multWellDefined invRight reflexive) j
      q' | inr 0=y-x = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder (multWellDefined x=y reflexive) reflexive xc<yc))
        where
          open Group additiveGroup
          f : inverse identity ∼ inverse (y + inverse x)
          f = inverseWellDefined additiveGroup 0=y-x
          g : identity ∼ (inverse y) + x
          g = transitive (symmetric (invIdentity additiveGroup)) (transitive f (transitive (transitive (invContravariant additiveGroup) groupIsAbelian) (wellDefined reflexive (invInv additiveGroup))))
          x=y : x ∼ y
          x=y = transferToRight additiveGroup (symmetric (transitive g groupIsAbelian))
      q'' : (0R + x) < ((y + Group.inverse additiveGroup x) + x)
      q'' = OrderedRing.orderRespectsAddition oRing q' x

  ringSwapNegatives : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x y : A} → (Group.inverse (Ring.additiveGroup R) x) < (Group.inverse (Ring.additiveGroup R) y) → y < x
  ringSwapNegatives {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} oRing {x} {y} -x<-y = SetoidPartialOrder.wellDefined pOrder (transitive (symmetric (Group.multAssoc additiveGroup)) (transitive (Group.wellDefined additiveGroup reflexive (Group.invLeft additiveGroup)) (Group.multIdentRight additiveGroup))) (Group.multIdentLeft additiveGroup) v
    where
      open Ring R
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      t : ((Group.inverse additiveGroup x) + y) < ((Group.inverse additiveGroup y) + y)
      t = OrderedRing.orderRespectsAddition oRing -x<-y y
      u : (y + (Group.inverse additiveGroup x)) < 0R
      u = SetoidPartialOrder.wellDefined pOrder (groupIsAbelian) (Group.invLeft additiveGroup) t
      v : ((y + (Group.inverse additiveGroup x)) + x) < (0R + x)
      v = OrderedRing.orderRespectsAddition oRing u x

  ringCanMultiplyByNegative : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x y c : A} → c < (Ring.0R R) → x < y → (y * c) < (x * c)
  ringCanMultiplyByNegative {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} oRing {x} {y} {c} c<0 x<y = ringSwapNegatives oRing u
    where
      open Ring R
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      p : (c + Group.inverse additiveGroup c) < (0R + Group.inverse additiveGroup c)
      p = OrderedRing.orderRespectsAddition oRing c<0 _
      0<-c : 0R < (Group.inverse additiveGroup c)
      0<-c = SetoidPartialOrder.wellDefined pOrder (Group.invRight additiveGroup) (Group.multIdentLeft additiveGroup) p
      t : (x * Group.inverse additiveGroup c) < (y * Group.inverse additiveGroup c)
      t = ringCanMultiplyByPositive oRing 0<-c x<y
      u : (Group.inverse additiveGroup (x * c)) < Group.inverse additiveGroup (y * c)
      u = SetoidPartialOrder.wellDefined pOrder (ringMinusExtracts R) (ringMinusExtracts R) t

  ringCanCancelNegative : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) → {x y c : A} → c < (Ring.0R R) → (x * c) < (y * c) → y < x
  ringCanCancelNegative {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} oRing {x} {y} {c} c<0 xc<yc = r
    where
      open Ring R
      open Setoid S
      open Group additiveGroup
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      p : 0R < ((y * c) + inverse (x * c))
      p = SetoidPartialOrder.wellDefined pOrder invRight reflexive (OrderedRing.orderRespectsAddition oRing xc<yc (inverse (x * c)))
      p1 : 0R < ((y * c) + ((inverse x) * c))
      p1 = SetoidPartialOrder.wellDefined pOrder reflexive (Group.wellDefined additiveGroup reflexive (transitive (inverseWellDefined additiveGroup multCommutative) (transitive (symmetric (ringMinusExtracts R)) multCommutative))) p
      p2 : 0R < ((y + inverse x) * c)
      p2 = SetoidPartialOrder.wellDefined pOrder reflexive (transitive (Group.wellDefined additiveGroup multCommutative multCommutative) (transitive (symmetric multDistributes) multCommutative)) p1
      q : (y + inverse x) < 0R
      q with SetoidTotalOrder.totality tOrder 0R (y + inverse x)
      q | inl (inl pr) = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.transitive pOrder bad c<0))
        where
          bad : 0R < c
          bad = ringCanCancelPositive oRing pr (SetoidPartialOrder.wellDefined pOrder (symmetric (transitive multCommutative (ringTimesZero R))) multCommutative p2)
      q | inl (inr pr) = pr
      q | inr 0=y-x = exFalso (SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.wellDefined pOrder (multWellDefined x=y reflexive) reflexive xc<yc))
        where
          x=y : x ∼ y
          x=y = transitive (symmetric multIdentLeft) (transitive (Group.wellDefined additiveGroup 0=y-x reflexive) (transitive (symmetric (Group.multAssoc additiveGroup)) (transitive (Group.wellDefined additiveGroup reflexive invLeft) multIdentRight)))
      r : y < x
      r = SetoidPartialOrder.wellDefined pOrder (transitive (symmetric (Group.multAssoc additiveGroup)) (transitive (Group.wellDefined additiveGroup reflexive (invLeft)) multIdentRight)) (Group.multIdentLeft additiveGroup) (OrderedRing.orderRespectsAddition oRing q x)
