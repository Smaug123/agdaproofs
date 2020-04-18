{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

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
open import Sequences
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Semirings.Definition
open import Functions.Definition
open import Fields.Orders.Total.Definition
open import Numbers.Primes.PrimeNumbers

module Fields.Orders.Limits.Lemmas {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {c} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {F : Field R} {pRing : PartiallyOrderedRing R pOrder} (oF : TotallyOrderedField F pRing) where

open Ring R
open TotallyOrderedField oF
open TotallyOrderedRing oRing
open PartiallyOrderedRing pRing
open import Rings.Orders.Total.Lemmas oRing
open import Rings.Orders.Total.AbsoluteValue oRing
open import Rings.Orders.Partial.Lemmas pRing
open SetoidTotalOrder total
open SetoidPartialOrder pOrder
open Group additiveGroup
open import Groups.Lemmas additiveGroup
open Setoid S
open Equivalence eq
open Field F
open import Fields.CauchyCompletion.Definition (TotallyOrderedField.oRing oF) F
open import Fields.Orders.Limits.Definition oF
open import Fields.Lemmas F
open import Fields.Orders.Total.Lemmas oF
open import Rings.Characteristic R
open import Rings.InitialRing R
open import Rings.Orders.Total.Cauchy oRing

private
  2!=3 : 2 ≡ 3 → False
  2!=3 ()

convergentSequenceCauchy : (nontrivial : 0R ∼ 1R → False) → {a : Sequence A} → {r : A} → a ~> r → cauchy a
convergentSequenceCauchy _ {a} {r} a->r e 0<e with halve (λ i → charNotN 1 (transitive (transitive +Associative identRight) i)) e
... | e/2 , prE/2 with a->r e/2 (halvePositive' prE/2 0<e)
... | N , pr = N , λ {m} {n} → ans m n
  where
    ans : (m n : ℕ) → N <N m → N <N n → abs (index a m + inverse (index a n)) < e
    ans m n N<m N<n = <WellDefined reflexive prE/2 (bothNearImpliesNear {r} e/2 (halvePositive' prE/2 0<e) (pr m N<m) (pr n N<n))
