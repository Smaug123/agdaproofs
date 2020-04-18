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
open import Functions.Definition
open import Rings.Definition
open import Fields.Fields
open import Fields.Orders.Partial.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Orders.Total.Archimedean {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {_<_ : A → A → Set c} {pOrder : SetoidPartialOrder S _<_} {F : Field R} (p : PartiallyOrderedField F pOrder) where

open Setoid S
open Equivalence eq
open Ring R
open Group additiveGroup
open import Groups.Lemmas additiveGroup
open import Groups.Cyclic.Definition additiveGroup
open import Groups.Cyclic.DefinitionLemmas additiveGroup
open import Groups.Orders.Archimedean (toGroup R (PartiallyOrderedField.oRing p))
open import Rings.Orders.Partial.Lemmas (PartiallyOrderedField.oRing p)
open import Rings.InitialRing R
open SetoidPartialOrder pOrder
open PartiallyOrderedRing (PartiallyOrderedField.oRing p)
open Field F

ArchimedeanField : Set (a ⊔ c)
ArchimedeanField = (x : A) → (0R < x) → Sg ℕ (λ n → x < (fromN n))

private
  lemma : (r : A) (N : ℕ) → (positiveEltPower 1R N * r) ∼ positiveEltPower r N
  lemma r zero = timesZero'
  lemma r (succ n) = transitive *DistributesOver+' (+WellDefined identIsIdent (lemma r n))

  findBound : (0<1 : 0R < 1R) → (r s : A) (N : ℕ) → (1R < r) → (s < positiveEltPower 1R N) → s < positiveEltPower r N
  findBound _ r s zero 1<r s<N = s<N
  findBound 0<1 r s (succ N) 1<r s<N = <Transitive s<N (<WellDefined (transitive *Commutative identIsIdent) (lemma r (succ N)) (ringCanMultiplyByPositive' (fromNPreservesOrder 0<1 (succIsPositive N)) 1<r))

archFieldToGrp : ((x y : A) → 0R < x → (x * y) ∼ 1R → 0R < y) → ArchimedeanField → Archimedean
archFieldToGrp reciprocalPositive a r s 0<r 0<s with allInvertible r (λ r=0 → irreflexive (<WellDefined reflexive r=0 0<r))
... | inv , prInv with a inv (reciprocalPositive r inv 0<r (transitive *Commutative prInv))
... | N , invBound with a s 0<s
... | Ns , nSBound = (Ns *N N) , <WellDefined reflexive (symmetric (elementPowerMultiplies (nonneg Ns) (nonneg N) r)) (findBound (<WellDefined reflexive (transitive *Commutative prInv) (orderRespectsMultiplication 0<r (reciprocalPositive r inv 0<r (transitive *Commutative prInv)))) (positiveEltPower r N) s Ns m nSBound)
  where
    m : 1R < positiveEltPower r N
    m = <WellDefined prInv (lemma r N) (ringCanMultiplyByPositive 0<r invBound)

archToArchField : 0R < 1R → Archimedean → ArchimedeanField
archToArchField 0<1 arch a 0<a with arch 1R a 0<1 0<a
... | N , pr = N , pr
