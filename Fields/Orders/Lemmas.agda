{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Rings.Definition
open import Rings.Order
open import Rings.Lemmas
open import Setoids.Setoids
open import Setoids.Orders
open import Orders
open import Rings.IntegralDomains
open import Functions
open import Sets.EquivalenceRelations
open import Fields.Fields
open import Fields.Orders.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Orders.Lemmas {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {o} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} {F : Field R} (oF : OrderedField F tOrder) where

open Ring R
open Group additiveGroup
open OrderedRing (OrderedField.oRing oF)
open import Rings.Orders.Lemmas (OrderedField.oRing oF)
open import Fields.Lemmas F
open Setoid S
open SetoidPartialOrder pOrder

clearDenominatorHalf : (x y 1/2 : A) → (1/2 + 1/2 ∼ 1R) → x < (y * 1/2) → (x + x) < y
clearDenominatorHalf x y 1/2 pr1/2 x<1/2y = <WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq *DistributesOver+) (Equivalence.transitive eq *Commutative (*WellDefined pr1/2 (Equivalence.reflexive eq)))) identIsIdent) (ringAddInequalities x<1/2y x<1/2y)

clearDenominatorHalf' : (x y 1/2 : A) → (1/2 + 1/2 ∼ 1R) → (x * 1/2) < y → x < (y + y)
clearDenominatorHalf' x y 1/2 pr1/2 1/2x<y = <WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq *DistributesOver+) (Equivalence.transitive eq (Equivalence.transitive eq *Commutative (*WellDefined pr1/2 (Equivalence.reflexive eq))) identIsIdent)) (Equivalence.reflexive eq) (ringAddInequalities 1/2x<y 1/2x<y)

halveInequality : (x y 1/2 : A) → (1/2 + 1/2 ∼ 1R) → (x + x) < y → x < (y * 1/2)
halveInequality x y 1/2 pr1/2 2x<y with SetoidTotalOrder.totality tOrder 0R 1R
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
