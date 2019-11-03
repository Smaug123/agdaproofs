{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Orders
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Groups
open import Groups.Lemmas
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Semirings.Definition

module Fields.CauchyCompletion.Approximation {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Ring R
open Group additiveGroup
open Field F

open import Fields.Lemmas F
open import Fields.Orders.Lemmas {F = F} record { oRing = order }
open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Partial.Lemmas pRing
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Addition order F charNot2
open import Fields.CauchyCompletion.Setoid order F charNot2
open import Fields.CauchyCompletion.Comparison order F charNot2

abstract

  chain : {a b : A} (c : CauchyCompletion) → (a r<C c) → (c <Cr b) → a < b
  chain {a} {b} c (betweenAC , (0<betweenAC ,, (Nac , prAC))) (betweenCB , (0<betweenCB ,, (Nb , prBC))) = SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<betweenAC a)) (<WellDefined groupIsAbelian (Equivalence.reflexive eq) (SetoidPartialOrder.<Transitive pOrder (prAC (succ Nac +N Nb) (le Nb (applyEquality succ (Semiring.commutative ℕSemiring Nb Nac)))) (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<betweenCB (index (Sequence.tail (CauchyCompletion.elts c)) (Nac +N Nb))))))) (prBC (succ Nac +N Nb) (le Nac refl))

  approxLemma : (a : CauchyCompletion) (e e/2 : A) → (0G < e) → (e/2 + e/2 ∼ e) → (m N : ℕ) → abs ((index (CauchyCompletion.elts a) m) + inverse (index (CauchyCompletion.elts a) N)) < e/2 → (e/2 + index (CauchyCompletion.elts a) m) < (index (CauchyCompletion.elts a) N + e)
  approxLemma a e e/2 0<e prE/2 m N ans with totality 0R ((index (CauchyCompletion.elts a) m) + inverse (index (CauchyCompletion.elts a) N))
  approxLemma a e e/2 0<e prE/2 m N ans | inl (inl x) with <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (invLeft))) identRight) groupIsAbelian (orderRespectsAddition ans (index (CauchyCompletion.elts a) N))
  ... | bl = <WellDefined groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) prE/2)) (orderRespectsAddition bl e/2)
  approxLemma a e e/2 0<e prE/2 m N ans | inl (inr x) with <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (invLeft))) identRight) (identLeft) (orderRespectsAddition x (index (CauchyCompletion.elts a) N))
  ... | bl = <WellDefined groupIsAbelian (Equivalence.reflexive eq) (ringAddInequalities bl (halfLess e/2 e 0<e prE/2))
  approxLemma a e e/2 0<e prE/2 m N ans | inr x with transferToRight additiveGroup (Equivalence.symmetric eq x)
  ... | bl = <WellDefined (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq bl)) groupIsAbelian (orderRespectsAddition (halfLess e/2 e 0<e prE/2) (index (CauchyCompletion.elts a) N))

  approximateAboveCrude : (a : CauchyCompletion) → Sg A (λ b → (a <Cr b))
  approximateAboveCrude a with CauchyCompletion.converges a 1R (0<1 (charNot2ImpliesNontrivial R charNot2))
  ... | N , conv = ((((index (CauchyCompletion.elts a) (succ N)) + 1R) + 1R) + 1R) , (1R , (0<1 (charNot2ImpliesNontrivial R charNot2) ,, (N , ans)))
    where
      ans : (m : ℕ) → (N <N m) → (1R + index (CauchyCompletion.elts a) m) < (((index (CauchyCompletion.elts a) (succ N) + 1R) + 1R) + 1R)
      ans m N<m with conv {m} {succ N} N<m (le 0 refl)
      ... | bl with totality 0G (index (CauchyCompletion.elts a) m + inverse (index (CauchyCompletion.elts a) (succ N)))
      ans m N<m | bl | inl (inl 0<am-aN) with <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (invLeft))) identRight) (Equivalence.reflexive eq) (orderRespectsAddition bl (index (CauchyCompletion.elts a) (succ N)))
      ... | am<1+an = <WellDefined (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) identLeft) groupIsAbelian) (Equivalence.transitive eq (+WellDefined groupIsAbelian (Equivalence.reflexive eq)) +Associative) (ringAddInequalities am<1+an (orderRespectsAddition (0<1 (charNot2ImpliesNontrivial R charNot2)) 1R))
      ans m N<m | bl | inl (inr am-aN<0) with <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invLeft)) identRight) identLeft (orderRespectsAddition am-aN<0 (index (CauchyCompletion.elts a) (succ N)))
      ... | am<aN = <WellDefined groupIsAbelian (Equivalence.reflexive eq) (orderRespectsAddition (SetoidPartialOrder.<Transitive pOrder am<aN (<WellDefined (Equivalence.reflexive eq) (+Associative) (<WellDefined identLeft groupIsAbelian (orderRespectsAddition (<WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities (0<1 (charNot2ImpliesNontrivial R charNot2)) (0<1 (charNot2ImpliesNontrivial R charNot2)))) (index (CauchyCompletion.elts a) (succ N)))))) 1R)
      ans m N<m | bl | inr 0=am-aN = <WellDefined (Equivalence.transitive eq (+WellDefined identLeft (Equivalence.reflexive eq)) identLeft) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (+WellDefined (Equivalence.transitive eq groupIsAbelian (+WellDefined (transferToRight additiveGroup (Equivalence.symmetric eq 0=am-aN)) (Equivalence.reflexive eq))) (Equivalence.reflexive eq)) +Associative)) (orderRespectsAddition (ringAddInequalities (0<1 (charNot2ImpliesNontrivial R charNot2)) (0<1 (charNot2ImpliesNontrivial R charNot2))) (1R + (index (CauchyCompletion.elts a) m)))

  rationalApproximatelyAbove : (a : CauchyCompletion) → (e : A) → (0G < e) → A
  rationalApproximatelyAbove a e 0<e with halve charNot2 e
  ... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
  ... | 0<e/2 with halve charNot2 e/2
  ... | e/4 , prE/4 with halvePositive e/4 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/4) 0<e/2)
  ... | 0<e/4 with CauchyCompletion.converges a e/4 0<e/4
  ... | N , cauchyBeyondN = index (CauchyCompletion.elts a) (succ N) + e/2

  rationalApproximatelyAboveIsAbove : (a : CauchyCompletion) (e : A) → (0<e : 0G < e) → a <Cr (rationalApproximatelyAbove a e 0<e)
  rationalApproximatelyAboveIsAbove a e 0<e with halve charNot2 e
  ... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
  ... | 0<e/2 with halve charNot2 e/2
  ... | e/4 , prE/4 with halvePositive e/4 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/4) 0<e/2)
  ... | 0<e/4 with CauchyCompletion.converges a e/4 0<e/4
  ... | N , cauchyBeyondN with halve charNot2 e/4
  ... | e/8 , prE/8 with halvePositive e/8 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/8) 0<e/4)
  ... | 0<e/8 with CauchyCompletion.converges a e/8 0<e/8
  ... | N2 , cauchyBeyondN2 = e/8 , (0<e/8 ,, ((N +N N2) , ans2))
    where
      ans2 : (m : ℕ) → N +N N2 <N m → (e/8 + index (CauchyCompletion.elts a) m) < (index (CauchyCompletion.elts a) (succ N) + e/2)
      ans2 m <m with cauchyBeyondN {m} {succ N} (inequalityShrinkLeft <m) (le 0 refl)
      ... | absam-aN<e/4 with totality 0R ((index (CauchyCompletion.elts a) m) + inverse (index (CauchyCompletion.elts a) (succ N)))
      ans2 m <m | am-aN<e/4 | inl (inl 0<am-aN) = SetoidPartialOrder.<Transitive pOrder (<WellDefined groupIsAbelian (Equivalence.transitive eq groupIsAbelian  +Associative) (orderRespectsAddition (<WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invLeft)) identRight) (Equivalence.reflexive eq) (orderRespectsAddition am-aN<e/4 (index (CauchyCompletion.elts a) (succ N)))) e/8)) (<WellDefined (Equivalence.reflexive eq) groupIsAbelian (orderRespectsAddition (<WellDefined (Equivalence.reflexive eq) prE/4 (orderRespectsAddition (halfLess e/8 e/4 0<e/4 prE/8) e/4)) (index (CauchyCompletion.elts a) (succ N))))
      ans2 m <m | -[am-aN]<e/4 | inl (inr am-aN<0) with <WellDefined (Equivalence.transitive eq +Associative (Equivalence.transitive eq (+WellDefined invLeft (Equivalence.reflexive eq)) identLeft)) (Equivalence.reflexive eq) (orderRespectsAddition (<WellDefined (Equivalence.reflexive eq) (invTwice additiveGroup _) (ringSwapNegatives' -[am-aN]<e/4)) (e/4 + e/8))
      ... | e/8<am-aN+e/4+e/8 = SetoidPartialOrder.<Transitive pOrder (orderRespectsAddition e/8<am-aN+e/4+e/8 (index (CauchyCompletion.elts a) m)) (<WellDefined (Equivalence.reflexive eq) groupIsAbelian (ringAddInequalities (<WellDefined (Equivalence.reflexive eq) identLeft (ringAddInequalities am-aN<0 (<WellDefined groupIsAbelian prE/4 (orderRespectsAddition (halfLess e/8 e/4 0<e/4 prE/8) e/4)))) am<aN))
        where
          am<aN : (index (CauchyCompletion.elts a) m) < (index (CauchyCompletion.elts a) (succ N))
          am<aN = <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) groupIsAbelian)) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) invRight) identRight)) identLeft (orderRespectsAddition am-aN<0 (index (CauchyCompletion.elts a) (succ N)))
      ans2 m <m | absam-aN<e/4 | inr 0=am-aN = <WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq groupIsAbelian (+WellDefined (transferToRight additiveGroup (Equivalence.symmetric eq 0=am-aN)) (Equivalence.reflexive eq))) (orderRespectsAddition {b = e/2} (SetoidPartialOrder.<Transitive pOrder (halfLess e/8 e/4 0<e/4 prE/8) (halfLess e/4 e/2 0<e/2 prE/4)) (index (CauchyCompletion.elts a) m))

  rationalApproximatelyAboveIsNear : (a : CauchyCompletion) (e : A) → (0<e : 0G < e) → (injection (rationalApproximatelyAbove a e 0<e) +C (-C a)) <C (injection e)
  rationalApproximatelyAboveIsNear a e 0<e with halve charNot2 e
  ... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
  ... | 0<e/2 with halve charNot2 e/2
  ... | e/4 , prE/4 with halvePositive e/4 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/4) 0<e/2)
  ... | 0<e/4 with CauchyCompletion.converges a e/4 0<e/4
  ... | N , cauchyBeyondN with halve charNot2 e/4
  ... | e/8 , prE/8 with halvePositive e/8 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/8) 0<e/4)
  ... | 0<e/8 with CauchyCompletion.converges a e/8 0<e/8
  ... | N8 , cauchyBeyondN8 with halve charNot2 e/8
  ... | e/16 , prE/16 with halvePositive e/16 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/16) 0<e/8)
  ... | 0<e/16 = ((e/2 + e/4) + e/8) , ((e/8 , (0<e/8 ,, ((N +N N8) , ans))) ,, (e/16 , (0<e/16 ,, (0 , t'))))
    where
      t' : (m : ℕ) → (0 <N m) → (((e/2 + e/4) + e/8) + e/16) < index (constSequence e) m
      t' m 0<m rewrite indexAndConst e m = <WellDefined (Equivalence.reflexive eq) prE/2 (<WellDefined (Equivalence.reflexive eq) (+WellDefined (Equivalence.reflexive eq) prE/4) (<WellDefined +Associative (Equivalence.symmetric eq +Associative) (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (<WellDefined (Equivalence.reflexive eq) prE/8 (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (halfLess e/16 e/8 0<e/8 prE/16) e/8))) (e/2 + e/4)))))
      ans : (m : ℕ) → (N +N N8) <N m → (e/8 + index (apply _+_ (constSequence (index (CauchyCompletion.elts a) (succ N) + e/2)) (map inverse (CauchyCompletion.elts a))) m) < ((e/2 + e/4) + e/8)
      ans m N<m rewrite indexAndApply (constSequence (index (CauchyCompletion.elts a) (succ N) + e/2)) (map inverse (CauchyCompletion.elts a)) _+_ {m} | indexAndConst (index (CauchyCompletion.elts a) (succ N) + e/2) m | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) = <WellDefined groupIsAbelian (+WellDefined groupIsAbelian (Equivalence.reflexive eq)) (orderRespectsAddition (<WellDefined (Equivalence.transitive eq groupIsAbelian (Equivalence.reflexive eq)) (Equivalence.reflexive eq) q) e/8)
        where
          am = index (CauchyCompletion.elts a) m
          aN = index (CauchyCompletion.elts a) (succ N)
          t : abs (am + inverse aN) < e/4
          t = cauchyBeyondN {m} {succ N} (inequalityShrinkLeft N<m) (le 0 refl)
          r : ((inverse am) + aN) < e/4
          r with t
          ... | f with totality 0G (am + inverse aN)
          r | am-aN<e/4 | inl (inl 0<am-aN) = SetoidPartialOrder.<Transitive pOrder (<WellDefined (Equivalence.transitive eq (invContravariant additiveGroup) (Equivalence.transitive eq groupIsAbelian (+WellDefined (Equivalence.reflexive eq) (invTwice additiveGroup _)))) (Equivalence.reflexive eq) (lemm2' _ 0<am-aN)) 0<e/4
          r | f | inl (inr x) = <WellDefined (Equivalence.transitive eq (invContravariant additiveGroup) (Equivalence.transitive eq groupIsAbelian (+WellDefined (Equivalence.reflexive eq) (invTwice additiveGroup _)))) (Equivalence.reflexive eq) f
          r | am-aN<e/4 | inr 0=am-aN = <WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq 0=am-aN) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq (invIdent additiveGroup)) (inverseWellDefined additiveGroup 0=am-aN)) (inverseWellDefined additiveGroup groupIsAbelian)) (invContravariant additiveGroup)) (+WellDefined (Equivalence.reflexive eq) (invTwice additiveGroup _)))) (Equivalence.reflexive eq) am-aN<e/4
          q : ((inverse (index (CauchyCompletion.elts a) m)) + (index (CauchyCompletion.elts a) (succ N) + e/2)) < (e/4 + e/2)
          q = <WellDefined (Equivalence.symmetric eq +Associative) (Equivalence.reflexive eq) (orderRespectsAddition r e/2)

  approximateAbove : (a : CauchyCompletion) → (ε : A) → (0G < ε) → Sg A (λ b → (a <Cr b) && (injection b +C (-C a)) <C (injection ε))
  approximateAbove a e 0<e = rationalApproximatelyAbove a e 0<e , (rationalApproximatelyAboveIsAbove a e 0<e ,, rationalApproximatelyAboveIsNear a e 0<e)

  approximateBelow : (a : CauchyCompletion) → (ε : A) → (0G < ε) → Sg A (λ b → (b r<C a) && (a +C (-C injection b)) <C (injection ε))
  approximateBelow a e 0<e with approximateAbove (-C a) e 0<e
  ... | x , ((deltaXAnd-A , (0<deltaXA ,, (NdeltaXA , prDeltaXA))) ,, (rationalNear , ((bound , (0<bound ,, (N , prBound))) ,, (bound2 , (0<bound2 ,, (N2 , prBound2)))))) = inverse x , ((deltaXAnd-A , (0<deltaXA ,, (NdeltaXA , λ m N<m → <WellDefined (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (cancel {m} (CauchyCompletion.elts a))) identRight)))))) (Equivalence.transitive eq +Associative (Equivalence.transitive eq (+WellDefined invRight (Equivalence.reflexive eq)) identLeft)) (orderRespectsAddition (prDeltaXA m N<m) (inverse x + (index (CauchyCompletion.elts a) m)))))) ,, (rationalNear , ((bound , (0<bound ,, (N , pr1))) ,, (bound2 , (0<bound2 ,, (N2 , prBound2))))))
    where
      cancel : {m : ℕ} (a : Sequence A) → (index (map inverse a) m) + (index a m) ∼ 0G
      cancel {m} a rewrite equalityCommutative (mapAndIndex a inverse m) = invLeft
      pr1 : (m : ℕ) → (N <N m) → (bound + index (apply _+_ (CauchyCompletion.elts a) (map inverse (constSequence (inverse x)))) m) < rationalNear
      pr1 m N<m with prBound m N<m
      ... | bl rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (constSequence (inverse x))) _+_ {m} | equalityCommutative (mapAndIndex (constSequence (inverse x)) inverse m) | indexAndConst x m | indexAndApply (constSequence x) (map inverse (map inverse (CauchyCompletion.elts a))) _+_ {m} | indexAndConst x m | equalityCommutative (mapAndIndex (map inverse (CauchyCompletion.elts a)) inverse m) | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) | indexAndConst (inverse x) m = <WellDefined (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq groupIsAbelian (+WellDefined (invTwice additiveGroup _) (Equivalence.symmetric eq (invTwice additiveGroup _))))) (Equivalence.reflexive eq) bl

  boundModulus : (a : CauchyCompletion) → Sg A (λ b → Sg ℕ (λ N → (m : ℕ) → (N <N m) → (abs (index (CauchyCompletion.elts a) m)) < b))
  boundModulus a with approximateBelow a 1R (0<1 (charNot2ImpliesNontrivial R charNot2))
  ... | below , (below<a ,, a-below<e) with approximateAbove a 1R (0<1 (charNot2ImpliesNontrivial R charNot2))
  ... | above , (a<above ,, above-a<e) with totality 0R below
  boundModulus a | below , (below<a ,, a-below<e) | above , (a<above ,, above-a<e) | inl (inl 0<below) with totality 0R above
  boundModulus a | below , ((belowBound , (0<belowBound ,, (Nbelow , prBelow))) ,, a-below<e) | above , ((bound , (0<bound ,, (N , ans))) ,, above-a<e) | inl (inl 0<below) | inl (inl 0<above) = above , ((N +N Nbelow) , λ m N<m → SetoidPartialOrder.<Transitive pOrder (res m N<m) (ans m (inequalityShrinkLeft N<m)))
    where
      res : (m : ℕ) → ((N +N Nbelow) <N m) → (abs (index (CauchyCompletion.elts a) m)) < (bound + index (CauchyCompletion.elts a) m)
      res m N<m with totality 0R (index (CauchyCompletion.elts a) m)
      res m N<m | inl (inl _) = <WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<bound (index (CauchyCompletion.elts a) m))
      res m N<m | inl (inr am<0) = exFalso (irreflexive (SetoidPartialOrder.<Transitive pOrder 0<below (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<belowBound below)) (prBelow m (inequalityShrinkRight N<m))) am<0)))
      res m N<m | inr 0=am = <WellDefined 0=am (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (+WellDefined (Equivalence.reflexive eq) 0=am)) 0<bound
  boundModulus a | below , (below<a ,, a-below<e) | above , (a<above ,, above-a<e) | inl (inl 0<below) | inl (inr above<0) = exFalso (irreflexive (SetoidPartialOrder.<Transitive pOrder 0<below (SetoidPartialOrder.<Transitive pOrder (chain a below<a a<above) above<0)))
  boundModulus a | below , (below<a ,, a-below<e) | above , (a<above ,, above-a<e) | inl (inl 0<below) | inr 0=above = exFalso (irreflexive (SetoidPartialOrder.<Transitive pOrder 0<below (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=above) (chain a below<a a<above))))
  boundModulus a | below , (below<a ,, a-below<e) | above , (a<above ,, above-a<e) | inl (inr below<0) with totality 0R above
  boundModulus a | below , (below<a ,, a-below<e) | above , (a<above ,, above-a<e) | inl (inr below<0) | inl (inl 0<above) with totality (inverse below) above
  boundModulus a | below , ((boundBelow , (0<boundBelow ,, (N , prBoundBelow))) ,, a-below<e) | above , ((boundAbove , (0<boundAbove ,, (Nabove , prBoundAbove))) ,, above-a<e) | inl (inr below<0) | inl (inl 0<above) | inl (inl -bel<ab) = above , ((N +N Nabove) , ans)
    where
      ans : (m : ℕ) → (N +N Nabove <N m) → abs (index (CauchyCompletion.elts a) m) < above
      ans m N<m with totality 0G (index (CauchyCompletion.elts a) m)
      ans m N<m | inl (inl 0<am) = SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<boundAbove (index (CauchyCompletion.elts a) m))) (prBoundAbove m (inequalityShrinkRight N<m))
      ans m N<m | inl (inr am<0) = SetoidPartialOrder.<Transitive pOrder (ringSwapNegatives' (prBoundBelow m (inequalityShrinkLeft N<m))) (SetoidPartialOrder.<Transitive pOrder (ringSwapNegatives' (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<boundBelow below))) -bel<ab)
      ans m N<m | inr 0=am = <WellDefined 0=am (Equivalence.reflexive eq) 0<above
  boundModulus a | below , ((boundBelow , (0<boundBelow ,, (N , prBoundBelow))) ,, a-below<e) | above , ((boundAbove , (0<boundAbove ,, (Nabove , prBoundAbove))) ,, above-a<e) | inl (inr below<0) | inl (inl 0<above) | inl (inr ab<-bel) = inverse below , ((N +N Nabove) , ans)
    where
      ans : (m : ℕ) → (N +N Nabove <N m) → abs (index (CauchyCompletion.elts a) m) < (inverse below)
      ans m N<m with totality 0G (index (CauchyCompletion.elts a) m)
      ans m N<m | inl (inl 0<am) = SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<boundAbove (index (CauchyCompletion.elts a) m))) (prBoundAbove m (inequalityShrinkRight N<m))) ab<-bel
      ans m N<m | inl (inr am<0) = ringSwapNegatives' (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<boundBelow below)) (prBoundBelow m (inequalityShrinkLeft N<m)))
      ans m N<m | inr 0=am = <WellDefined 0=am (Equivalence.reflexive eq) (lemm2 below below<0)
  boundModulus a | below , ((boundBelow , (0<boundBelow ,, (N , prBoundBelow))) ,, a-below<e) | above , ((boundAbove , (0<boundAbove ,, (Nabove , prBoundAbove))) ,, above-a<e) | inl (inr below<0) | inl (inl 0<above) | inr -bel=ab = above , ((N +N Nabove) , ans)
    where
      ans : (m : ℕ) → (N +N Nabove <N m) → abs (index (CauchyCompletion.elts a) m) < above
      ans m N<m with totality 0G (index (CauchyCompletion.elts a) m)
      ans m N<m | inl (inl 0<am) = SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<boundAbove (index (CauchyCompletion.elts a) m))) (prBoundAbove m (inequalityShrinkRight N<m))
      ans m N<m | inl (inr am<0) = <WellDefined (Equivalence.reflexive eq) (-bel=ab) (ringSwapNegatives' (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<boundBelow below)) (prBoundBelow m (inequalityShrinkLeft N<m))))
      ans m N<m | inr 0=am = <WellDefined 0=am (Equivalence.reflexive eq) 0<above
  boundModulus a | below , ((boundBelow , (0<boundBelow ,, (N , prBoundBelow))) ,, a-below<e) | above , ((boundAbove , (0<boundAbove ,, (Nabove , prBoundAbove))) ,, above-a<e) | inl (inr below<0) | inl (inr above<0) = inverse below , ((N +N Nabove) , ans)
    where
      ans : (m : ℕ) → ((N +N Nabove) <N m) → abs (index (CauchyCompletion.elts a) m) < inverse below
      ans m N<m with totality 0R (index (CauchyCompletion.elts a) m)
      ans m N<m | inl (inl 0<am) = exFalso (irreflexive {0G} (SetoidPartialOrder.<Transitive pOrder 0<am (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<boundAbove (index (CauchyCompletion.elts a) m))) (prBoundAbove m (inequalityShrinkRight N<m))) above<0)))
      ans m N<m | inl (inr am<0) = ringSwapNegatives' (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<boundBelow below)) (prBoundBelow m (inequalityShrinkLeft N<m)))
      ans m N<m | inr 0=am = exFalso (irreflexive {0G} (<WellDefined (Equivalence.symmetric eq 0=am) (Equivalence.reflexive eq) (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<boundAbove (index (CauchyCompletion.elts a) m))) (prBoundAbove m (inequalityShrinkRight N<m))) above<0)))
  boundModulus a | below , ((boundBelow , (0<boundBelow ,, (N , prBoundBelow))) ,, a-below<e) | above , ((boundAbove , (0<boundAbove ,, (Nabove , prBoundAbove))) ,, above-a<e) | inl (inr below<0) | inr 0=above = inverse below , ((N +N Nabove) , ans)
    where
      ans : (m : ℕ) → ((N +N Nabove) <N m) → abs (index (CauchyCompletion.elts a) m) < inverse below
      ans m N<m with totality 0R (index (CauchyCompletion.elts a) m)
      ans m N<m | inl (inl 0<am) = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=above) (SetoidPartialOrder.<Transitive pOrder 0<am (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<boundAbove (index (CauchyCompletion.elts a) m))) (prBoundAbove m (inequalityShrinkRight N<m))))))
      ans m N<m | inl (inr am<0) = ringSwapNegatives' (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<boundBelow below)) (prBoundBelow m (inequalityShrinkLeft N<m)))
      ans m N<m | inr 0=am = <WellDefined 0=am (Equivalence.reflexive eq) (lemm2 _ below<0)
  boundModulus a | below , ((boundBelow , ((boundBelowDiff ,, (Nb , ansBelow)))) ,, a-below<e) | above , ((bound , (0<bound ,, (N , ans))) ,, above-a<e) | inr 0=below = above , ((N +N Nb) , λ m N<m → SetoidPartialOrder.<Transitive pOrder (res m N<m) (ans m (inequalityShrinkLeft N<m)))
    where
      res : (m : ℕ) → (N +N Nb) <N m → (abs (index (CauchyCompletion.elts a) m)) < (bound + index (CauchyCompletion.elts a) m)
      res m N<m with totality 0R (index (CauchyCompletion.elts a) m)
      res m N<m | inl (inl 0<am) = <WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<bound (index (CauchyCompletion.elts a) m))
      res m N<m | inl (inr am<0) = exFalso (irreflexive (<WellDefined (Equivalence.symmetric eq 0=below) (Equivalence.reflexive eq) (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition boundBelowDiff below)) (ansBelow m (inequalityShrinkRight N<m))) am<0)))
      res m N<m | inr 0=am = <WellDefined 0=am (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (+WellDefined (Equivalence.reflexive eq) 0=am)) 0<bound
