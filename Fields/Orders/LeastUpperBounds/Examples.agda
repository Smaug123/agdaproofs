{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Sets.EquivalenceRelations
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Fields
open import Groups.Definition
open import Functions

module Fields.Orders.LeastUpperBounds.Examples {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {_} {c} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {pOrderedRing : PartiallyOrderedRing R pOrder} (orderedRing : TotallyOrderedRing pOrderedRing) (F : Field R) (isNontrivial : Setoid._∼_ S (Ring.0R R) (Ring.1R R) → False) where

open PartiallyOrderedRing pOrderedRing
open Setoid S
open Equivalence eq
open SetoidTotalOrder (TotallyOrderedRing.total orderedRing)
open Field F
open Ring R
open SetoidPartialOrder pOrder
open Group additiveGroup
open import Rings.Orders.Partial.Lemmas pOrderedRing
open import Rings.Orders.Total.Lemmas orderedRing
open import Fields.Orders.LeastUpperBounds.Definition pOrder

charNot2 : Setoid._∼_ S (Ring.1R R + Ring.1R R) (Ring.0R R) → False
charNot2 = orderedImpliesCharNot2 nontrivial

openIntervalPred : (a : A) → (b : A) → a < b → A → Set _
openIntervalPred a b a<b x = (a < x) && (x < b)

openInterval : (a : A) → (b : A) → (a<b : a < b) → subset S (openIntervalPred a b a<b)
openInterval a b a<b x=y (a<x ,, x<b) = SetoidPartialOrder.<WellDefined pOrder reflexive x=y a<x ,, SetoidPartialOrder.<WellDefined pOrder x=y reflexive x<b

1/2 : A
1/2 with allInvertible (1R + 1R) charNot2
... | n , _ = n

1/2Is1/2 : 1/2 * (1R + 1R) ∼ 1R
1/2Is1/2 with allInvertible (1R + 1R) charNot2
... | n , pr = pr

1/2Is1/2' : (1/2 + 1/2) ∼ 1R
1/2Is1/2' = transitive (+WellDefined (symmetric identIsIdent) (symmetric identIsIdent)) (transitive (transitive (symmetric *DistributesOver+') *Commutative) 1/2Is1/2)

halfHalves : (a : A) → ((a + a) * 1/2) ∼ a
halfHalves a = transitive *DistributesOver+' (transitive (transitive (transitive (symmetric *DistributesOver+) (*WellDefined reflexive 1/2Is1/2')) *Commutative) identIsIdent)

0<1/2 : 0R < 1/2
0<1/2 = halvePositive 1/2 (<WellDefined reflexive (symmetric (transitive (symmetric (transitive *DistributesOver+ (+WellDefined (transitive *Commutative identIsIdent) (transitive *Commutative identIsIdent)))) 1/2Is1/2)) (0<1 nontrivial))

min<mean : (a b : A) → a < b → a < ((a + b) * 1/2)
min<mean a b a<b = <WellDefined (transitive *DistributesOver+' (transitive (+WellDefined *Commutative *Commutative) (transitive (symmetric *DistributesOver+') (transitive (*WellDefined 1/2Is1/2' reflexive) identIsIdent)))) reflexive a+a<a+b
  where
    a+a<a+b : ((a + a) * 1/2) < ((a + b) * 1/2)
    a+a<a+b = ringCanMultiplyByPositive 0<1/2 (<WellDefined reflexive groupIsAbelian (orderRespectsAddition a<b a))

mean<max : (a b : A) → a < b → ((a + b) * 1/2) < b
mean<max a b a<b = <WellDefined reflexive (halfHalves b) a+b<b+b
  where
    a+b<b+b : ((a + b) * 1/2) < ((b + b) * 1/2)
    a+b<b+b = ringCanMultiplyByPositive 0<1/2 (orderRespectsAddition a<b b)

example1 : (a b : A) (a<b : a < b) → LeastUpperBound (openInterval a b a<b) b
LeastUpperBound.upperBound (example1 a b a<b) y (a<y ,, y<b) = inl y<b
LeastUpperBound.leastUpperBound (example1 a b a<b) y isUpperBound with totality b y
LeastUpperBound.leastUpperBound (example1 a b a<b) y isUpperBound | inl (inl x) = inl x
LeastUpperBound.leastUpperBound (example1 a b a<b) y isUpperBound | inl (inr y<b) = exFalso false
  where
    betterBound : A
    betterBound = (y + b) * 1/2
    p1 : ((y + b) * 1/2) < ((b + b) * 1/2)
    p1 = ringCanMultiplyByPositive 0<1/2 (orderRespectsAddition y<b b)
    p2 : betterBound < b
    p2 = <WellDefined reflexive (transitive (*WellDefined (transitive (symmetric (+WellDefined identIsIdent identIsIdent)) (transitive (+WellDefined *Commutative *Commutative) (symmetric *DistributesOver+))) reflexive) (transitive (symmetric *Associative) (transitive (transitive (*WellDefined reflexive (transitive *Commutative 1/2Is1/2)) *Commutative) identIsIdent))) p1
    a<y : a < y
    a<y with isUpperBound ((a + b) * 1/2) (min<mean a b a<b ,, mean<max a b a<b)
    a<y | inl a+b/2<y = <Transitive (min<mean a b a<b) a+b/2<y
    a<y | inr a+b/2=y = <WellDefined reflexive a+b/2=y (min<mean a b a<b)
    p3 : ((a + a) * 1/2) < ((y + b) * 1/2)
    p3 = ringCanMultiplyByPositive 0<1/2 (ringAddInequalities a<y a<b)
    a<betterBound : a < betterBound
    a<betterBound = <WellDefined (halfHalves a) reflexive p3
    bad : (betterBound < y) || (betterBound ∼ y)
    bad = isUpperBound betterBound (a<betterBound ,, p2)
    false : False
    false with bad
    false | inl mean<y with min<mean y b y<b
    ... | y<mean = irreflexive (<Transitive y<mean mean<y)
    false | inr x = irreflexive (<WellDefined (symmetric x) reflexive (min<mean y b y<b))
LeastUpperBound.leastUpperBound (example1 a b a<b) y isUpperBound | inr x = inr x
