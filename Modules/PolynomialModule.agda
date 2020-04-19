{-# OPTIONS --safe --warning=error --without-K #-}

open import Sets.EquivalenceRelations
open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
open import Modules.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Lists.Lists
open import Vectors
open import Groups.Definition
open import Orders.Total.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Rings.Homomorphisms.Definition

module Modules.PolynomialModule {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open import Groups.Polynomials.Definition additiveGroup
open import Groups.Polynomials.Group additiveGroup
open import Rings.Polynomial.Multiplication R
open import Rings.Polynomial.Evaluation R
open import Rings.Polynomial.Ring R
open import Rings.Lemmas polyRing

polynomialRingModule : Module R abelianUnderlyingGroup (λ a b → _*P_ (polyInjection a) b)
Module.dotWellDefined (polynomialRingModule) r=s t=u = Ring.*WellDefined polyRing (r=s ,, record {}) t=u
Module.dotDistributesLeft (polynomialRingModule) {r} {s} {t} = Ring.*DistributesOver+ polyRing {polyInjection r} {s} {t}
Module.dotDistributesRight (polynomialRingModule) {r} {s} {t} = Ring.*DistributesOver+' polyRing {polyInjection r} {polyInjection s} {t}
Module.dotAssociative (polynomialRingModule) {r} {s} {t} = Equivalence.transitive (Setoid.eq naivePolySetoid) (Ring.*WellDefined polyRing m (Equivalence.reflexive (Setoid.eq naivePolySetoid) {t})) (Equivalence.symmetric (Setoid.eq naivePolySetoid) (Ring.*Associative polyRing {polyInjection r} {polyInjection s} {t}))
  where
    m : Setoid._∼_ naivePolySetoid ((r * s) :: []) ((r * s) :: (([] +P []) +P (0R :: [])))
    m = Equivalence.reflexive (Setoid.eq S) ,, (Equivalence.reflexive (Setoid.eq S) ,, record {})
Module.dotIdentity (polynomialRingModule) = Ring.identIsIdent polyRing

open import Modules.Span polynomialRingModule

polynomialBasis : ℕ → NaivePoly
polynomialBasis zero = polyInjection 1R
polynomialBasis (succ a) = 0R :: polynomialBasis a

count : (n : ℕ) → Vec ℕ n
count zero = []
count (succ n) = 0 ,- vecMap succ (count n)

lemma : {d : _} {D : Set d} → (f : D → List A) → {n : ℕ} → (m : Vec D n) (r : Vec A n)  → Setoid._∼_ naivePolySetoid (dot (vecMap (λ i → 0R :: f i) m) r) (0R :: dot (vecMap f m) r)
lemma f [] [] = reflexive ,, record {}
  where
    open Setoid S
    open Equivalence eq
lemma f (m ,- ms) (r ,- rs) rewrite refl {x = 0} = transitive (+WellDefined {(r * 0R) :: (((map (_*_ r) (f m)) +P []) +P (0R :: []))} {_} {(r * 0R) :: (((map (_*_ r) (f m)) +P []) +P (0R :: []))} (reflexive {(r * 0R) :: (((map (_*_ r) (f m)) +P []) +P (0R :: []))}) (lemma f ms rs)) (Equivalence.transitive (Setoid.eq S) (Group.identRight additiveGroup) (Ring.timesZero R) ,, +WellDefined {((map (_*_ r) (f m)) +P []) +P (0R :: [])} {dot (vecMap f ms) rs} {(r :: []) *P f m} {dot (vecMap f ms) rs} t (reflexive {dot (vecMap f ms) rs}))
  where
    open Setoid naivePolySetoid
    open Equivalence eq
    open Group polyGroup
    lemm : (v : List A) → polysEqual (map (_*_ r) v) ((r :: []) *P v)
    lemm [] = record {}
    lemm (x :: v) = Equivalence.reflexive (Setoid.eq S) ,, symmetric (transitive (+WellDefined {map (_*_ r) v +P []} {0R :: []} {_} {[]} reflexive (Equivalence.reflexive (Setoid.eq S) ,, record {})) (transitive (identRight {(map (_*_ r) v) +P []}) (identRight {map (_*_ r) v})))
    t : ((map (_*_ r) (f m) +P []) +P (0R :: [])) ∼ ((r :: []) *P f m)
    t = transitive (+WellDefined {map (_*_ r) (f m) +P []} {0R :: []} {_} {[]} reflexive (Equivalence.reflexive (Setoid.eq S) ,, record {})) (transitive (identRight {map (_*_ r) (f m) +P []}) (transitive (identRight {map (_*_ r) (f m)}) (lemm (f m))))

identityMap : (v : List A) → Setoid._∼_ naivePolySetoid (dot (vecMap polynomialBasis (count (length v))) (listToVec v)) v
identityMap [] = record {}
identityMap (x :: v) rewrite vecMapCompose succ polynomialBasis (count (length v)) = transitive (+WellDefined {(x * 1R) :: Group.0G additiveGroup :: []} {dot (vecMap (λ i → Group.0G additiveGroup :: polynomialBasis i) (count (length v))) (listToVec v)} {(x * 1R) :: 0R :: []} {0R :: dot (vecMap polynomialBasis (count (length v))) (listToVec v)} (reflexive {(x * 1R) :: 0R :: []}) (lemma polynomialBasis (count (length v)) (listToVec v))) (Equivalence.transitive (Setoid.eq S) (Group.identRight additiveGroup) (Equivalence.transitive (Setoid.eq S) *Commutative identIsIdent) ,, transitive (+WellDefined {0R :: []} {dot (vecMap polynomialBasis (count (length v))) (listToVec v)} {[]} (Equivalence.reflexive (Setoid.eq S) ,, record {}) reflexive) (transitive identLeft (identityMap v)))
  where
    open Group polyGroup
    open Setoid naivePolySetoid
    open Equivalence eq

polynomialBasisSpans : Spans polynomialBasis
polynomialBasisSpans m = length m , ((count (length m) ,, listToVec m) , identityMap m)

{-
private
  indepWithZero : {n : ℕ} (rs : Vec ℕ n) (indicesDistinct : {a b : ℕ} → (a<n : a <N succ n) (b<n : b <N succ n) → vecIndex (0 ,- rs) a a<n ≡ vecIndex (0 ,- rs) b b<n → a ≡ b) (b : A) (bs : Vec A n) (dotZero : Setoid._∼_ naivePolySetoid (((b * 1R) :: 0R :: []) +P (dot (vecMap polynomialBasis rs) bs)) []) → (nonzero : {a : ℕ} → (a<n : a <N n) → 0 <N vecIndex rs a a<n) → Setoid._∼_ S 0R b && _=V_ additiveGroup (vecPure 0R) bs
  indepWithZero rs indicesDistinct b bs dotZero indicesNonzero = symmetric b=0 ,, {!!}
    where
      open Setoid S
      open Equivalence eq
      open Group additiveGroup
      t : (inducedFunction (((b * 1R) :: 0R :: []) +P (dot (vecMap polynomialBasis rs) bs)) 0R) ∼ 0R
      t = inducedFunctionWellDefined dotZero 0R
      u : ((inducedFunction ((b * 1R) :: 0R :: []) 0R) + inducedFunction (dot (vecMap polynomialBasis rs) bs) 0R) ∼ 0R
      u = transitive (symmetric (GroupHom.groupHom (RingHom.groupHom (inducedFunctionIsHom 0R)) {((b * 1R) :: 0R :: [])} {dot (vecMap polynomialBasis rs) bs})) t
      b=0 : b ∼ 0R
      b=0 = transitive (symmetric (transitive (+WellDefined (transitive (transitive (transitive (+WellDefined reflexive (transitive *Commutative timesZero)) identRight) *Commutative) identIsIdent) {!imageOfIdentityIsIdentity (RingHom.groupHom (inducedFunctionIsHom 0R))!}) (identRight {b}))) u

polynomialBasisIndependent : Independent polynomialBasis
polynomialBasisIndependent [] indicesDistinct [] dotZero = record {}
polynomialBasisIndependent {succ n} (zero ,- rs) indicesDistinct (b ,- bs) dotZero = indepWithZero rs indicesDistinct b bs dotZero t
  where
    t : {a : ℕ} (a<n : a <N n) → 0 <N vecIndex rs a a<n
    t {a} a<n with TotalOrder.totality ℕTotalOrder 0 (vecIndex rs a a<n)
    t {a} a<n | inl (inl x) = x
    t {a} a<n | inr x with indicesDistinct {succ a} {0} (succPreservesInequality a<n) (succIsPositive n) (equalityCommutative x)
    ... | ()
polynomialBasisIndependent (succ r ,- rs) indicesDistinct (b ,- bs) dotZero = {!!}
  where
    rearr : {!!}
    rearr = {!!}

-}
