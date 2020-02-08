{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Rings.Lemmas
open import Setoids.Setoids
open import Setoids.Orders
open import Rings.IntegralDomains.Definition
open import Functions
open import Sets.EquivalenceRelations
open import Fields.Fields
open import Fields.Orders.Total.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Fields.Orders.Lemmas {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {o} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {F : Field R} {pRing : PartiallyOrderedRing R pOrder} (oF : TotallyOrderedField F pRing) where

abstract

  open import Rings.InitialRing R
  open Ring R
  open PartiallyOrderedRing pRing
  open Group additiveGroup
  open TotallyOrderedRing (TotallyOrderedField.oRing oF)
  open SetoidTotalOrder total
  open import Rings.Orders.Partial.Lemmas pRing
  open import Rings.Orders.Total.Lemmas (TotallyOrderedField.oRing oF)
  open import Fields.Lemmas F
  open Setoid S
  open SetoidPartialOrder pOrder
  open Equivalence eq
  open Field F

  clearDenominatorHalf : (x y 1/2 : A) → (1/2 + 1/2 ∼ 1R) → x < (y * 1/2) → (x + x) < y
  clearDenominatorHalf x y 1/2 pr1/2 x<1/2y = <WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq *DistributesOver+) (Equivalence.transitive eq *Commutative (*WellDefined pr1/2 (Equivalence.reflexive eq)))) identIsIdent) (ringAddInequalities x<1/2y x<1/2y)

  clearDenominatorHalf' : (x y 1/2 : A) → (1/2 + 1/2 ∼ 1R) → (x * 1/2) < y → x < (y + y)
  clearDenominatorHalf' x y 1/2 pr1/2 1/2x<y = <WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq *DistributesOver+) (Equivalence.transitive eq (Equivalence.transitive eq *Commutative (*WellDefined pr1/2 (Equivalence.reflexive eq))) identIsIdent)) (Equivalence.reflexive eq) (ringAddInequalities 1/2x<y 1/2x<y)

  halveInequality : (x y 1/2 : A) → (1/2 + 1/2 ∼ 1R) → (x + x) < y → x < (y * 1/2)
  halveInequality x y 1/2 pr1/2 2x<y with totality 0R 1R
  ... | inl (inl 0<1') = <WellDefined (halfHalves 1/2 pr1/2) (Equivalence.reflexive eq) (ringCanMultiplyByPositive {_} {_} {1/2} (halvePositive 1/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr1/2) (0<1 λ bad → irreflexive {0R} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq bad) 0<1')))) 2x<y)
  ... | inl (inr 1<0) = <WellDefined (halfHalves 1/2 pr1/2) (Equivalence.reflexive eq) (ringCanMultiplyByPositive {_} {_} {1/2} (halvePositive 1/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr1/2) (0<1 λ bad → irreflexive {0R} (<WellDefined (Equivalence.symmetric eq bad) (Equivalence.reflexive eq) 1<0)))) 2x<y)
  ... | inr 0=1 = exFalso (irreflexive {0R} (<WellDefined (oneZeroImpliesAllZero R 0=1) (oneZeroImpliesAllZero R 0=1) 2x<y))

  halveInequality' : (x y 1/2 : A) → (1/2 + 1/2 ∼ 1R) → x < (y + y) → (x * 1/2) < y
  halveInequality' x y 1/2 pr1/2 x<2y with halveInequality (inverse y) (inverse x) 1/2 pr1/2 (<WellDefined (invContravariant additiveGroup) (Equivalence.reflexive eq) (ringSwapNegatives' x<2y))
  ... | bl = ringSwapNegatives (<WellDefined (Equivalence.reflexive eq) (ringMinusExtracts' R) bl)

  dense : (charNot2 : ((1R + 1R) ∼ 0R) → False) {x y : A} → (x < y) → Sg A (λ i → (x < i) && (i < y))
  dense charNot2 {x} {y} x<y with halve charNot2 1R
  dense charNot2 {x} {y} x<y | 1/2 , pr1/2 = ((x + y) * 1/2) , (halveInequality x (x + y) 1/2 pr1/2 (<WellDefined (Equivalence.reflexive eq) groupIsAbelian (orderRespectsAddition x<y x)) ,, halveInequality' (x + y) y 1/2 pr1/2 (orderRespectsAddition x<y y))

  halfLess : (e/2 e : A) → (0<e : 0G < e) → (pr : e/2 + e/2 ∼ e) → e/2 < e
  halfLess e/2 e 0<e pr with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr) 0<e)
  ... | 0<e/2 = <WellDefined identLeft pr (orderRespectsAddition 0<e/2 e/2)

  inversePositiveIsPositive : {a b : A} → (a * b) ∼ 1R → 0R < b → 0R < a
  inversePositiveIsPositive {a} {b} ab=1 0<b with totality 0R a
  inversePositiveIsPositive {a} {b} ab=1 0<b | inl (inl 0<a) = 0<a
  inversePositiveIsPositive {a} {b} ab=1 0<b | inl (inr a<0) with <WellDefined *Commutative (Equivalence.reflexive eq) (posTimesNeg _ _ 0<b a<0)
  ... | ab<0 = exFalso (1<0False (<WellDefined ab=1 (Equivalence.reflexive eq) ab<0))
  inversePositiveIsPositive {a} {b} ab=1 0<b | inr 0=a = exFalso (irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (oneZeroImpliesAllZero R 0=1) 0<b))
    where
      0=1 : 0R ∼ 1R
      0=1 = Equivalence.transitive eq (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a) (Equivalence.reflexive eq)) (Equivalence.transitive eq *Commutative timesZero))) ab=1

  halvesEqual : ((1R + 1R ∼ 0R) → False) → (1/2 1/2' : A) → (1/2 + 1/2) ∼ 1R → (1/2' + 1/2') ∼ 1R → 1/2 ∼ 1/2'
  halvesEqual charNot2 1/2 1/2' pr1 pr2 = Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq identIsIdent) (Equivalence.transitive eq *Commutative (*WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.symmetric eq p1) *Commutative)))) (Equivalence.transitive eq r (Equivalence.transitive eq (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq *Commutative p1)) *Commutative) (identIsIdent)))
    where
      p : 1/2 * (1R + 1R) ∼ 1/2' * (1R + 1R)
      p = Equivalence.transitive eq *DistributesOver+ (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (+WellDefined (Equivalence.transitive eq *Commutative identIsIdent) (Equivalence.transitive eq *Commutative identIsIdent)) pr1) (Equivalence.transitive eq (Equivalence.symmetric eq pr2) (+WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative identIsIdent)) (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative identIsIdent))))) (Equivalence.symmetric eq *DistributesOver+))
      x : A
      x with Field.allInvertible F (1R + 1R) charNot2
      ... | y , _ = y
      p1 : (x * (1R + 1R)) ∼ 1R
      p1 with Field.allInvertible F (1R + 1R) charNot2
      ... | _ , pr = pr
      q : ((1/2 * (1R + 1R)) * x) ∼ ((1/2' * (1R + 1R)) * x)
      q = *WellDefined p (Equivalence.reflexive eq)
      r : (1/2 * ((1R + 1R) * x)) ∼ (1/2' * ((1R + 1R) * x))
      r = Equivalence.transitive eq *Associative (Equivalence.transitive eq q (Equivalence.symmetric eq *Associative))

  private
    orderedFieldIntDom : {a b : A} → (a * b ∼ 0R) → (a ∼ 0R) || (b ∼ 0R)
    orderedFieldIntDom {a} {b} ab=0 with totality 0R a
    ... | inl (inl x) = inr (Equivalence.transitive eq (Equivalence.transitive eq (symmetric identIsIdent) (*WellDefined q reflexive)) p')
      where
        a!=0 : (a ∼ Group.0G additiveGroup) → False
        a!=0 pr = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (symmetric pr) reflexive x)
        invA : A
        invA = underlying (Field.allInvertible F a a!=0)
        q : 1R ∼ (invA * a)
        q with Field.allInvertible F a a!=0
        ... | invA , pr = symmetric pr
        p : invA * (a * b) ∼ invA * Group.0G additiveGroup
        p = *WellDefined reflexive ab=0
        p' : (invA * a) * b ∼ Group.0G additiveGroup
        p' = Equivalence.transitive eq (symmetric *Associative) (Equivalence.transitive eq p (Ring.timesZero R))
    orderedFieldIntDom {a} {b} ab=0 | inl (inr x) = inr (Equivalence.transitive eq (Equivalence.transitive eq (symmetric identIsIdent) (*WellDefined q reflexive)) p')
      where
        a!=0 : (a ∼ Group.0G additiveGroup) → False
        a!=0 pr = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder reflexive (symmetric pr) x)
        invA : A
        invA = underlying (Field.allInvertible F a a!=0)
        q : 1R ∼ (invA * a)
        q with Field.allInvertible F a a!=0
        ... | invA , pr = symmetric pr
        p : invA * (a * b) ∼ invA * Group.0G additiveGroup
        p = *WellDefined reflexive ab=0
        p' : (invA * a) * b ∼ Group.0G additiveGroup
        p' = Equivalence.transitive eq (symmetric *Associative) (Equivalence.transitive eq p (Ring.timesZero R))
    orderedFieldIntDom {a} {b} ab=0 | inr x = inl (Equivalence.symmetric (Setoid.eq S) x)

  orderedFieldIsIntDom :  IntegralDomain R
  IntegralDomain.intDom orderedFieldIsIntDom = decidedIntDom R orderedFieldIntDom
  IntegralDomain.nontrivial orderedFieldIsIntDom pr = Field.nontrivial F (Equivalence.symmetric (Setoid.eq S) pr)

  fromNIncreasing : (n : ℕ) → (fromN n) < (fromN (succ n))
  fromNIncreasing zero = <WellDefined reflexive (symmetric identRight) (0<1 nontrivial)
  fromNIncreasing (succ n) = <WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (fromNIncreasing n) 1R)

  fromNPreservesOrder : {a b : ℕ} → (a <N b) → (fromN a) < (fromN b)
  fromNPreservesOrder {zero} {succ zero} a<b = fromNIncreasing 0
  fromNPreservesOrder {zero} {succ (succ b)} a<b = <Transitive (fromNPreservesOrder (succIsPositive b)) (fromNIncreasing (succ b))
  fromNPreservesOrder {succ a} {succ b} a<b = <WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (fromNPreservesOrder (canRemoveSuccFrom<N a<b)) 1R)

  charZero : (n : ℕ) → (0R ∼ (fromN (succ n))) → False
  charZero n 0=sn = irreflexive (<WellDefined 0=sn reflexive (fromNPreservesOrder (succIsPositive n)))
  charZero' : (n : ℕ) → ((fromN (succ n)) ∼ 0R) → False
  charZero' n pr = charZero n (symmetric pr)
