{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Functions
open import Groups.Groups
open import Groups.GroupsLemmas
open import Rings.RingDefinition
open import Setoids.Setoids
open import Setoids.Orders

module Rings.RingLemmas where
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
