{-# OPTIONS --safe --warning=error --without-K #-}

open import Sets.EquivalenceRelations
open import Numbers.Naturals.Semiring
open import Numbers.Integers.Definition
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Groups.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Setoids.Setoids
open import Functions
open import Rings.Definition
open import Fields.Fields
open import Fields.Orders.Total.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Orders.Total.Archimedean {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {_<_ : A → A → Set c} {pOrder : SetoidPartialOrder S _<_} {p : PartiallyOrderedRing R pOrder} {F : Field R} (t : TotallyOrderedField F p) where

open Setoid S
open Equivalence eq
open Ring R
open Group additiveGroup
open import Groups.Lemmas additiveGroup
open import Groups.Cyclic.Definition additiveGroup
open import Groups.Cyclic.DefinitionLemmas additiveGroup
open import Groups.Orders.Archimedean (toGroup R p)
open import Rings.Orders.Partial.Lemmas p
open import Rings.InitialRing R
open SetoidPartialOrder pOrder
open PartiallyOrderedRing p
open SetoidTotalOrder (TotallyOrderedRing.total (TotallyOrderedField.oRing t))
open import Rings.Orders.Total.Lemmas (TotallyOrderedField.oRing t)
open Field F

ArchimedeanField : Set (a ⊔ c)
ArchimedeanField = (x : A) → (0R < x) → Sg ℕ (λ n → x < (fromN n))

private
  lemma : (r : A) (N : ℕ) → (positiveEltPower 1R N * r) ∼ positiveEltPower r N
  lemma r zero = timesZero'
  lemma r (succ n) = transitive *DistributesOver+' (+WellDefined identIsIdent (lemma r n))

  findBound : (r s : A) (N : ℕ) → (1R < r) → (s < positiveEltPower 1R N) → s < positiveEltPower r N
  findBound r s zero 1<r s<N = s<N
  findBound r s (succ N) 1<r s<N = <Transitive s<N (<WellDefined (transitive *Commutative identIsIdent) (lemma r (succ N)) (ringCanMultiplyByPositive' (fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial 1<r)) (succIsPositive N)) 1<r))

archFieldToGrp : ArchimedeanField → Archimedean
archFieldToGrp a r s 0<r 0<s with totality r s
archFieldToGrp a r s 0<r 0<s | inl (inr s<r) = 1 , <WellDefined reflexive (symmetric identRight) s<r
archFieldToGrp a r s 0<r 0<s | inr r=s = 2 , <WellDefined (transitive identLeft r=s) (+WellDefined reflexive (symmetric identRight)) (orderRespectsAddition 0<r r)
... | inl (inl r<s) with allInvertible r (λ r=0 → irreflexive (<WellDefined reflexive r=0 0<r))
... | inv , prInv with a inv (reciprocalPositive r inv 0<r (transitive *Commutative prInv))
... | N , invBound with a s 0<s
... | Ns , nSBound = (Ns *N N) , <WellDefined reflexive (symmetric (elementPowerMultiplies (nonneg Ns) (nonneg N) r)) (findBound (positiveEltPower r N) s Ns m nSBound)
  where
    m : 1R < positiveEltPower r N
    m = <WellDefined prInv (lemma r N) (ringCanMultiplyByPositive 0<r invBound)

archToArchField : Archimedean → ArchimedeanField
archToArchField arch a 0<a with arch 1R a (0<1 (anyComparisonImpliesNontrivial 0<a)) 0<a
... | N , pr = N , pr
