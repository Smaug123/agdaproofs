{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Fields.CauchyCompletion.Definition {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open TotallyOrderedRing order
open Ring R
open Group additiveGroup
open Field F

open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.Cauchy order
open import Groups.Lemmas additiveGroup

cauchyWellDefined : {s1 s2 : Sequence A} → ((m : ℕ) → index s1 m ∼ index s2 m) → cauchy s1 → cauchy s2
cauchyWellDefined {s1} {s2} prop c e 0<e with c e 0<e
... | N , pr = N , λ {m} {n} N<m N<n → <WellDefined (absWellDefined _ _ (+WellDefined (prop m) (inverseWellDefined (prop n)))) reflexive (pr N<m N<n)

record CauchyCompletion : Set (m ⊔ o) where
  field
    elts : Sequence A
    converges : cauchy elts

injection : A → CauchyCompletion
CauchyCompletion.elts (injection a) = constSequence a
CauchyCompletion.converges (injection a) = λ ε 0<e → 0 , λ {m} {n} _ _ → <WellDefined (symmetric (identityOfIndiscernablesRight _∼_ (absWellDefined (index (constSequence a) m + inverse (index (constSequence a) n)) 0R (t m n)) absZero)) reflexive 0<e
  where
    t : (m n : ℕ) → index (constSequence a) m + inverse (index (constSequence a) n) ∼ 0R
    t m n = identityOfIndiscernablesLeft _∼_ (identityOfIndiscernablesLeft _∼_ invRight (equalityCommutative (applyEquality (λ i → a + inverse i) (indexAndConst a n)))) (applyEquality (_+ inverse (index (constSequence a) n)) (equalityCommutative (indexAndConst a m)))

-- Some slightly odd things here relating to equality rather than equivalence. Ultimately this is here so we can say Q → R is a genuine injection, not just a setoid one.
private
  lemma : {x y : CauchyCompletion} → x ≡ y → CauchyCompletion.elts x ≡ CauchyCompletion.elts y
  lemma {x} {.x} refl = refl

CInjection' : Injection injection
CInjection' pr = headInjective (lemma pr)
