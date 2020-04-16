{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Orders.Total.Definition
open import Rings.IntegralDomains.Definition

module Rings.Orders.Total.AbsoluteValue {n m p : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} {pOrderRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pOrderRing) where

open Ring R
open Group additiveGroup
open Setoid S
open SetoidPartialOrder pOrder
open TotallyOrderedRing order
open SetoidTotalOrder total
open PartiallyOrderedRing pOrderRing
open import Rings.Lemmas R
open import Rings.Orders.Partial.Lemmas pOrderRing
open import Rings.Orders.Total.Lemmas order

abs : A → A
abs a with totality 0R a
abs a | inl (inl 0<a) = a
abs a | inl (inr a<0) = inverse a
abs a | inr 0=a = a

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

absZeroImpliesZero : {a : A} → abs a ∼ 0R → a ∼ 0R
absZeroImpliesZero {a} a=0 with totality 0R a
absZeroImpliesZero {a} a=0 | inl (inl 0<a) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) a=0 0<a))
absZeroImpliesZero {a} a=0 | inl (inr a<0) = Equivalence.symmetric eq (lemm3 (inverse a) a (Equivalence.symmetric eq invLeft) (Equivalence.symmetric eq a=0))
absZeroImpliesZero {a} a=0 | inr 0=a = a=0

addingAbsCannotShrink : {a b : A} → 0G < b → 0G < ((abs a) + b)
addingAbsCannotShrink {a} {b} 0<b with totality 0G a
addingAbsCannotShrink {a} {b} 0<b | inl (inl x) = <WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities x 0<b)
addingAbsCannotShrink {a} {b} 0<b | inl (inr x) = <WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities (lemm2 a x) 0<b)
addingAbsCannotShrink {a} {b} 0<b | inr x = <WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.symmetric eq identLeft) (+WellDefined x (Equivalence.reflexive eq))) 0<b

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

a-bPos : {a b : A} → ((a ∼ b) → False) → 0R < abs (a + inverse b)
a-bPos {a} {b} a!=b with totality 0R (a + inverse b)
a-bPos {a} {b} a!=b | inl (inl x) = x
a-bPos {a} {b} a!=b | inl (inr x) = lemm2 _ x
a-bPos {a} {b} a!=b | inr x = exFalso (a!=b (transferToRight additiveGroup (Equivalence.symmetric eq x)))
