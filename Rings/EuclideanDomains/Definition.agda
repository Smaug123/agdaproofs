{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Rings.IntegralDomains.Definition
open import Orders

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.EuclideanDomains.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Divisible.Definition R
open Setoid S
open Equivalence eq
open Ring R
open Group additiveGroup

record DivisionAlgorithmResult (norm : {a : A} → ((a ∼ 0R) → False) → ℕ) {x y : A} (x!=0 : (x ∼ 0R) → False) (y!=0 : (y ∼ 0R) → False) : Set (a ⊔ b) where
  field
    quotient : A
    rem : A
    remSmall : (rem ∼ 0R) || Sg ((rem ∼ 0R) → False) (λ rem!=0 → (norm rem!=0) <N (norm y!=0))
    divAlg : x ∼ ((quotient * y) + rem)

record DivisionAlgorithmResult' (norm : (a : A) → ℕ) (x y : A) : Set (a ⊔ b) where
  field
    quotient : A
    rem : A
    remSmall : (rem ∼ 0R) || ((norm rem) <N (norm y))
    divAlg : x ∼ ((quotient * y) + rem)

record EuclideanDomain : Set (a ⊔ lsuc b) where
  field
    isIntegralDomain : IntegralDomain R
    norm : {a : A} → ((a ∼ 0R) → False) → ℕ
    normSize : {a b : A} → (a!=0 : (a ∼ 0R) → False) → (b!=0 : (b ∼ 0R) → False) → (c : A) → b ∼ (a * c) → (norm a!=0) ≤N (norm b!=0)
    divisionAlg : {a b : A} → (a!=0 : (a ∼ 0R) → False) → (b!=0 : (b ∼ 0R) → False) → DivisionAlgorithmResult norm a!=0 b!=0
  normWellDefined : {a : A} → (p1 p2 : (a ∼ 0R) → False) → norm p1 ≡ norm p2
  normWellDefined {a} p1 p2 with normSize p1 p2 1R (symmetric (transitive *Commutative identIsIdent))
  normWellDefined {a} p1 p2 | inl n1<n2 with normSize p2 p1 1R (symmetric (transitive *Commutative identIsIdent))
  normWellDefined {a} p1 p2 | inl n1<n2 | inl n2<n1 = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder n1<n2 n2<n1))
  normWellDefined {a} p1 p2 | inl n1<n2 | inr n2=n1 = equalityCommutative n2=n1
  normWellDefined {a} p1 p2 | inr n1=n2 = n1=n2
  normWellDefined' : {a b : A} → (a ∼ b) → (a!=0 : (a ∼ 0R) → False) → (b!=0 : (b ∼ 0R) → False) → norm a!=0 ≡ norm b!=0
  normWellDefined' a=b a!=0 b!=0 with normSize a!=0 b!=0 1R (symmetric (transitive *Commutative (transitive identIsIdent a=b)))
  normWellDefined' a=b a!=0 b!=0 | inl a<b with normSize b!=0 a!=0 1R (symmetric (transitive *Commutative (transitive identIsIdent (symmetric a=b))))
  normWellDefined' a=b a!=0 b!=0 | inl a<b | inl b<a = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder a<b b<a))
  normWellDefined' a=b a!=0 b!=0 | inl a<b | inr n= = equalityCommutative n=
  normWellDefined' a=b a!=0 b!=0 | inr n= = n=

record EuclideanDomain' : Set (a ⊔ lsuc b) where
  field
    isIntegralDomain : IntegralDomain R
    norm : A → ℕ
    normWellDefined : {a b : A} → (a ∼ b) → norm a ≡ norm b
    normSize : (a b : A) → (a ∣ b) → ((b ∼ 0R) → False) → norm a ≤N (norm b)
    divisionAlg : (a b : A) → ((b ∼ 0R) → False) → DivisionAlgorithmResult' norm a b

normEquiv : (e : EuclideanDomain) (decidableZero : (a : A) → (a ∼ 0R) || ((a ∼ 0R) → False)) → A → ℕ
normEquiv e decidableZero a with decidableZero a
... | inl a=0 = 0
... | inr a!=0 = EuclideanDomain.norm e a!=0

normSizeEquiv : (e : EuclideanDomain) (decidableZero : (a : A) → (a ∼ 0R) || ((a ∼ 0R) → False)) (a b : A) → (a ∣ b) → ((b ∼ 0R) → False) → normEquiv e decidableZero a ≤N normEquiv e decidableZero b
normSizeEquiv e decidableZero a b (c , ac=b) b!=0 = ans
  where
    abstract
      a!=0 : (a ∼ 0R) → False
      a!=0 a=0 = b!=0 (transitive (symmetric ac=b) (transitive (*WellDefined a=0 reflexive) (transitive *Commutative timesZero)))
    normIs : normEquiv e decidableZero a ≡ EuclideanDomain.norm e a!=0
    normIs with decidableZero a
    normIs | inl a=0 = exFalso (a!=0 a=0)
    normIs | inr a!=0' = EuclideanDomain.normWellDefined e a!=0' a!=0
    normIs' : normEquiv e decidableZero b ≡ EuclideanDomain.norm e b!=0
    normIs' with decidableZero b
    normIs' | inl b=0 = exFalso (b!=0 b=0)
    normIs' | inr b!=0' = EuclideanDomain.normWellDefined e b!=0' b!=0
    ans : (normEquiv e decidableZero a) ≤N (normEquiv e decidableZero b)
    ans with EuclideanDomain.normSize e a!=0 b!=0 c (symmetric ac=b)
    ans | inl n<Nn = inl (identityOfIndiscernablesLeft _<N_ (identityOfIndiscernablesRight _<N_ n<Nn (equalityCommutative normIs')) (equalityCommutative normIs))
    ans | inr n=n = inr (transitivity normIs (transitivity n=n (equalityCommutative normIs')))

divisionAlgEquiv : (e : EuclideanDomain) (decidableZero : (a : A) → (a ∼ 0R) || ((a ∼ 0R) → False)) → (a b : A) → ((b ∼ 0R) → False) → DivisionAlgorithmResult' (normEquiv e decidableZero) a b
divisionAlgEquiv e decidableZero a b b!=0 with decidableZero a
divisionAlgEquiv e decidableZero a b b!=0 | inl a=0 = record { quotient = 0R ; rem = 0R ; remSmall = inl reflexive ; divAlg = transitive a=0 (transitive (symmetric identLeft) (+WellDefined (symmetric (transitive *Commutative timesZero)) reflexive)) }
divisionAlgEquiv e decidableZero a b b!=0 | inr a!=0 with EuclideanDomain.divisionAlg e a!=0 b!=0
divisionAlgEquiv e decidableZero a b b!=0 | inr a!=0 | record { quotient = quotient ; rem = rem ; remSmall = inl x ; divAlg = divAlg } = record { quotient = quotient ; rem = rem ; remSmall = inl x ; divAlg = divAlg }
divisionAlgEquiv e decidableZero a b b!=0 | inr a!=0 | record { quotient = quotient ; rem = rem ; remSmall = inr (rem!=0 , pr) ; divAlg = divAlg } = record { quotient = quotient ; rem = rem ; remSmall = inr (identityOfIndiscernablesLeft _<N_ (identityOfIndiscernablesRight _<N_ pr (equalityCommutative normIs')) (equalityCommutative normIs)) ; divAlg = divAlg }
  where
    normIs : normEquiv e decidableZero rem ≡ EuclideanDomain.norm e rem!=0
    normIs with decidableZero rem
    normIs | inl rem=0 = exFalso (rem!=0 rem=0)
    normIs | inr rem!=0' = EuclideanDomain.normWellDefined e rem!=0' rem!=0
    normIs' : normEquiv e decidableZero b ≡ EuclideanDomain.norm e b!=0
    normIs' with decidableZero b
    normIs' | inl b=0 = exFalso (b!=0 b=0)
    normIs' | inr b!=0' = EuclideanDomain.normWellDefined e b!=0' b!=0

normWellDefined : (e : EuclideanDomain) (decidableZero : (a : A) → (a ∼ 0R) || ((a ∼ 0R) → False)) {a b : A} (a=b : a ∼ b) → normEquiv e decidableZero a ≡ normEquiv e decidableZero b
normWellDefined e decidableZero {a} {b} a=b with decidableZero a
normWellDefined e decidableZero {a} {b} a=b | inl a=0 with decidableZero b
normWellDefined e decidableZero {a} {b} a=b | inl a=0 | inl b=0 = refl
normWellDefined e decidableZero {a} {b} a=b | inl a=0 | inr b!=0 = exFalso (b!=0 (transitive (symmetric a=b) a=0))
normWellDefined e decidableZero {a} {b} a=b | inr a!=0 with decidableZero b
normWellDefined e decidableZero {a} {b} a=b | inr a!=0 | inl b=0 = exFalso (a!=0 (transitive a=b b=0))
normWellDefined e decidableZero {a} {b} a=b | inr a!=0 | inr b!=0 = EuclideanDomain.normWellDefined' e a=b a!=0 b!=0

eucDomsEquiv : (decidableZero : (a : A) → (a ∼ 0R) || ((a ∼ 0R) → False)) → EuclideanDomain → EuclideanDomain'
eucDomsEquiv decidableZero e = record { isIntegralDomain = EuclideanDomain.isIntegralDomain e ; norm = normEquiv e decidableZero ; normSize = normSizeEquiv e decidableZero ; divisionAlg = divisionAlgEquiv e decidableZero ; normWellDefined = normWellDefined e decidableZero }
