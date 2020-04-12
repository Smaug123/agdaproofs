{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
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
open import Numbers.Modulo.Definition
open import Semirings.Definition
open import Orders.Total.Definition
open import Sequences

module Rings.Orders.Total.BaseExpansion {a m p : _} {A : Set a} {S : Setoid {a} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} {pOrderRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pOrderRing) {n : ℕ} (1<n : 1 <N n) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open SetoidPartialOrder pOrder
open TotallyOrderedRing order
open SetoidTotalOrder total
open PartiallyOrderedRing pOrderRing
open import Rings.Lemmas R
open import Rings.Orders.Partial.Lemmas pOrderRing
open import Rings.Orders.Total.Lemmas order
open import Rings.InitialRing R

record FloorIs (a : A) (n : ℕ) : Set (m ⊔ p) where
  field
    prBelow : fromN n <= a
    prAbove : a < fromN (succ n)

addOneToFloor : {a : A} {n : ℕ} → FloorIs a n → FloorIs (a + 1R) (succ n)
FloorIs.prBelow (addOneToFloor record { prBelow = (inl x) ; prAbove = prAbove }) = inl (<WellDefined groupIsAbelian reflexive (orderRespectsAddition x 1R))
FloorIs.prBelow (addOneToFloor record { prBelow = (inr x) ; prAbove = prAbove }) = inr (transitive groupIsAbelian (+WellDefined x reflexive))
FloorIs.prAbove (addOneToFloor record { prBelow = x ; prAbove = prAbove }) = <WellDefined reflexive groupIsAbelian (orderRespectsAddition prAbove 1R)

private
  0<n : {x y : A} → (x < y) → 0R < fromN n
  0<n x<y = fromNPreservesOrder (anyComparisonImpliesNontrivial x<y) (lessTransitive (succIsPositive 0) 1<n)

  floorWellDefinedLemma : {a : A} {n1 n2 : ℕ} → FloorIs a n1 → FloorIs a n2 → n1 <N n2 → False
  floorWellDefinedLemma {a} {n1} {n2} record { prAbove = prAbove1 } record { prBelow = inl prBelow } n1<n2 with TotalOrder.totality ℕTotalOrder (succ n1) n2
  ... | inl (inl n1+1<n2) = irreflexive (<Transitive prAbove1 (<Transitive (fromNPreservesOrder (anyComparisonImpliesNontrivial prBelow) n1+1<n2) prBelow))
  ... | inl (inr n2<n1+1) = noIntegersBetweenXAndSuccX n1 n1<n2 n2<n1+1
  ... | inr refl = irreflexive (<Transitive prAbove1 prBelow)
  floorWellDefinedLemma {a} {n1} {n2} record { prBelow = (inl x) ; prAbove = prAbove1 } record { prBelow = (inr eq) ; prAbove = _ } n1<n2 with TotalOrder.totality ℕTotalOrder (succ n1) n2
  ... | inl (inl n1+1<n2) = irreflexive (<Transitive prAbove1 (<WellDefined reflexive eq (fromNPreservesOrder (anyComparisonImpliesNontrivial prAbove1) n1+1<n2)))
  ... | inl (inr n2<n1+1) = noIntegersBetweenXAndSuccX n1 n1<n2 n2<n1+1
  ... | inr refl = irreflexive (<WellDefined reflexive eq prAbove1)
  floorWellDefinedLemma {a} {n1} {n2} record { prBelow = (inr x) ; prAbove = prAbove1 } record { prBelow = (inr eq) ; prAbove = _ } n1<n2 = lessIrreflexive {n1} (fromNPreservesOrder' (anyComparisonImpliesNontrivial prAbove1) (<WellDefined reflexive (transitive eq (symmetric x)) (fromNPreservesOrder (anyComparisonImpliesNontrivial prAbove1) n1<n2)))

  floorWellDefined : {a : A} {n1 n2 : ℕ} → FloorIs a n1 → FloorIs a n2 → n1 ≡ n2
  floorWellDefined {a} {n1} {n2} record { prBelow = prBelow1 ; prAbove = prAbove1 } record { prBelow = prBelow ; prAbove = prAbove } with TotalOrder.totality ℕTotalOrder n1 n2
  ... | inr x = x
  floorWellDefined {a} {n1} {n2} f1 f2 | inl (inl x) = exFalso (floorWellDefinedLemma f1 f2 x)
  floorWellDefined {a} {n1} {n2} f1 f2 | inl (inr x) = exFalso (floorWellDefinedLemma f2 f1 x)

  floorWellDefined' : {a b : A} {n : ℕ} → (a ∼ b) → FloorIs a n → FloorIs b n
  FloorIs.prBelow (floorWellDefined' {a} {b} {n} a=b record { prBelow = (inl x) ; prAbove = s }) = inl (<WellDefined reflexive a=b x)
  FloorIs.prBelow (floorWellDefined' {a} {b} {n} a=b record { prBelow = (inr x) ; prAbove = s }) = inr (transitive x a=b)
  FloorIs.prAbove (floorWellDefined' {a} {b} {n} a=b record { prBelow = t ; prAbove = s }) = <WellDefined a=b reflexive s

  computeFloor' : {k : ℕ} → (fuel : ℕ) → k +N fuel ≡ n → (a : A) → 0R < a → a < fromN k → Sg ℕ (FloorIs a)
  computeFloor' {zero} zero refl a 0<a a<f = exFalso (lessIrreflexive (lessTransitive 1<n (succIsPositive 0)))
  computeFloor' {zero} (succ k) pr a 0<a a<f = exFalso (irreflexive (<Transitive 0<a a<f))
  computeFloor' {succ k} n pr a 0<a a<f with totality 1R a
  ... | inl (inr a<1) = 0 , (record { prAbove = <WellDefined reflexive (symmetric identRight) a<1 ; prBelow = inl 0<a })
  ... | inr 1=a = 1 , (record { prAbove = <WellDefined (transitive identRight 1=a) reflexive (fromNPreservesOrder (anyComparisonImpliesNontrivial 0<a) {1} (le 0 refl)) ; prBelow = inr (transitive identRight 1=a) })
  ... | inl (inl 1<a) with computeFloor' {k} (succ n) (transitivity (transitivity (Semiring.commutative ℕSemiring k (succ n)) (applyEquality succ (Semiring.commutative ℕSemiring n k))) pr) (a + inverse 1R) (moveInequality 1<a) (<WellDefined reflexive (transitive groupIsAbelian (transitive +Associative (transitive (+WellDefined invLeft reflexive) identLeft))) (orderRespectsAddition a<f (inverse 1R)))
  ... | N , snd = succ N , floorWellDefined' (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) (addOneToFloor snd)

computeFloor : (a : A) → 0R < a → a < fromN n → Sg (ℤn n (lessTransitive (succIsPositive 0) 1<n)) (λ z → FloorIs a (ℤn.x z))
computeFloor a 0<a a<n with computeFloor' {n} 0 (Semiring.sumZeroRight ℕSemiring n) a 0<a a<n
... | floor , record { prBelow = inl p ; prAbove = prAbove } = record { x = floor ; xLess = fromNPreservesOrder' (anyComparisonImpliesNontrivial 0<a) (<Transitive p a<n) } , record { prBelow = inl p ; prAbove = prAbove }
... | floor , record { prBelow = inr p ; prAbove = prAbove } = record { x = floor ; xLess = fromNPreservesOrder' (anyComparisonImpliesNontrivial 0<a) (<WellDefined (symmetric p) reflexive a<n) } , record { prBelow = inr p ; prAbove = prAbove }

firstDigit : (a : A) → 0R < a → a < 1R → ℤn n (lessTransitive (succIsPositive 0) 1<n)
firstDigit a 0<a a<1 = underlying (computeFloor (a * fromN n) (orderRespectsMultiplication 0<a (0<n 0<a)) (<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1)))

baseNExpansion : (a : A) → 0R < a → a < 1R → Sequence (ℤn n (lessTransitive (succIsPositive 0) 1<n))
Sequence.head (baseNExpansion a 0<a a<1) = firstDigit a 0<a a<1
Sequence.tail (baseNExpansion a 0<a a<1) with computeFloor (a * fromN n) (orderRespectsMultiplication 0<a (0<n 0<a)) (<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1))
... | record { x = x ; xLess = xLess } , record { prBelow = inl prB ; prAbove = prA } = baseNExpansion ((a * fromN n) + inverse (fromN x)) (moveInequality prB) (<WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) (orderRespectsAddition prA (inverse (fromN x))))
... | record { x = x ; xLess = xLess } , record { prBelow = inr prB ; prAbove = prA } = constSequence (record { x = 0 ; xLess = lessTransitive (succIsPositive 0) 1<n })
