{-# OPTIONS --allow-unsolved-metas --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Groups
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Fields.CauchyCompletion.Field {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open PartiallyOrderedRing pRing
open SetoidPartialOrder pOrder
open Equivalence eq
open SetoidTotalOrder (TotallyOrderedRing.total order)
open Field F
open Group (Ring.additiveGroup R)

open import Rings.Orders.Total.Cauchy order
open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.AbsoluteValue order
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Multiplication order F
open import Fields.CauchyCompletion.Addition order F
open import Fields.CauchyCompletion.Setoid order F
open import Fields.CauchyCompletion.Group order F
open import Fields.CauchyCompletion.Ring order F
open import Fields.CauchyCompletion.Comparison order F

Cnontrivial : (pr : Setoid._∼_ cauchyCompletionSetoid (injection (Ring.0R R)) (injection (Ring.1R R))) → False
Cnontrivial pr with pr (Ring.1R R) (0<1 nontrivial)
Cnontrivial pr | N , b with b {succ N} (le 0 refl)
... | bl rewrite indexAndApply (constSequence 0G) (map inverse (constSequence (Ring.1R R))) _+_ {N} | indexAndConst 0G N | equalityCommutative (mapAndIndex (constSequence (Ring.1R R)) inverse N) | indexAndConst (Ring.1R R) N = irreflexive {Ring.1R R} (<WellDefined (Equivalence.transitive eq (absWellDefined _ _ identLeft) (Equivalence.transitive eq (Equivalence.symmetric eq (absNegation (Ring.1R R))) abs1Is1)) (Equivalence.reflexive eq) bl)

boundedMap : A → A
boundedMap a with totality 0G a
boundedMap a | inl (inl x) = underlying (allInvertible a λ pr → irreflexive (<WellDefined (Equivalence.reflexive eq) pr x))
boundedMap a | inl (inr x) = underlying (allInvertible a λ pr → irreflexive (<WellDefined pr (Equivalence.reflexive eq) x))
boundedMap a | inr x = Ring.1R R

-- TODO: make a real which is equivalent by approximating from above;
-- make a real which is equivalent by approximating from below.
-- Use not-zero to show that one of those sequences must pass 0 at some point.
aNonzeroImpliesBounded : (a : CauchyCompletion) → (Setoid._∼_ cauchyCompletionSetoid a (injection 0G) → False) → (a <Cr 0G) || 0G r<C a
aNonzeroImpliesBounded a a!=0 = {!!}

1/aConverges : (a : CauchyCompletion) → (Setoid._∼_ cauchyCompletionSetoid a (injection 0G) → False) → cauchy (map boundedMap (CauchyCompletion.elts a))
1/aConverges a a!=0 e 0<e = {!!}

1/a : (a : CauchyCompletion) → (Setoid._∼_ cauchyCompletionSetoid a (injection 0G) → False) → CauchyCompletion
1/a a a!=0 = record { elts = map boundedMap (CauchyCompletion.elts a) ; converges = 1/aConverges a a!=0 }

1/a*a=1 : (a : CauchyCompletion) (pr : Setoid._∼_ cauchyCompletionSetoid a (injection 0G) → False) → Setoid._∼_ cauchyCompletionSetoid ((1/a a pr) *C a) (injection (Ring.1R R))
1/a*a=1 a a!=0 e 0<e = {!!}

CField : Field CRing
Field.allInvertible CField a a!=0 = (1/a a a!=0) , 1/a*a=1 a a!=0
Field.nontrivial CField = Cnontrivial
