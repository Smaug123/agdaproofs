{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Vectors
open import Lists.Lists
open import Maybe
open import Rings.Homomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Polynomial.Evaluation {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open Setoid S
open Equivalence eq
open Group additiveGroup
open import Groups.Polynomials.Definition additiveGroup
open import Groups.Polynomials.Addition additiveGroup
open import Rings.Polynomial.Ring R
open import Rings.Polynomial.Multiplication R

inducedFunction : NaivePoly → A → A
inducedFunction [] a = 0R
inducedFunction (x :: p) a = x + (a * inducedFunction p a)

inducedFunctionMult : (as : NaivePoly) (b c : A) → inducedFunction (map (_*_ b) as) c ∼ (inducedFunction as c) * b
inducedFunctionMult [] b c = symmetric (transitive *Commutative timesZero)
inducedFunctionMult (x :: as) b c = transitive (transitive (+WellDefined reflexive (transitive (transitive (*WellDefined reflexive (inducedFunctionMult as b c)) *Associative) *Commutative)) (symmetric *DistributesOver+)) *Commutative

inducedFunctionWellDefined : {a b : NaivePoly} → polysEqual a b → (c : A) → inducedFunction a c ∼ inducedFunction b c
inducedFunctionWellDefined {[]} {[]} a=b c = reflexive
inducedFunctionWellDefined {[]} {x :: b} (fst ,, snd) c = symmetric (transitive (+WellDefined fst (transitive (*WellDefined reflexive (symmetric (inducedFunctionWellDefined {[]} {b} snd c))) (timesZero {c}))) identRight)
inducedFunctionWellDefined {a :: as} {[]} (fst ,, snd) c = transitive (+WellDefined fst reflexive) (transitive identLeft (transitive (*WellDefined reflexive (inducedFunctionWellDefined {as} {[]} snd c)) (timesZero {c})))
inducedFunctionWellDefined {a :: as} {b :: bs} (fst ,, snd) c = +WellDefined fst (*WellDefined reflexive (inducedFunctionWellDefined {as} {bs} snd c))

inducedFunctionGroupHom : {x y : NaivePoly} → (a : A) → inducedFunction (x +P y) a ∼ (inducedFunction x a + inducedFunction y a)
inducedFunctionGroupHom {[]} {[]} a = symmetric identLeft
inducedFunctionGroupHom {[]} {x :: y} a rewrite mapId y = symmetric identLeft
inducedFunctionGroupHom {x :: xs} {[]} a rewrite mapId xs = symmetric identRight
inducedFunctionGroupHom {x :: xs} {y :: ys} a = transitive (symmetric +Associative) (transitive (+WellDefined reflexive (transitive (transitive (+WellDefined reflexive (transitive (*WellDefined reflexive (transitive (inducedFunctionGroupHom {xs} {ys} a) groupIsAbelian)) *DistributesOver+)) +Associative) groupIsAbelian)) +Associative)

inducedFunctionRingHom : (r s : NaivePoly) (a : A) → inducedFunction (r *P s) a ∼ (inducedFunction r a * inducedFunction s a)
inducedFunctionRingHom [] s a = symmetric (transitive *Commutative timesZero)
inducedFunctionRingHom (x :: xs) [] a = symmetric timesZero
inducedFunctionRingHom (b :: bs) (c :: cs) a = transitive (+WellDefined reflexive (*WellDefined reflexive (inducedFunctionGroupHom {map (_*_ b) cs +P map (_*_ c) bs} {0G :: (bs *P cs)} a))) (transitive (+WellDefined reflexive (*WellDefined reflexive (+WellDefined (inducedFunctionGroupHom {map (_*_ b) cs} {map (_*_ c) bs} a) identLeft))) (transitive (transitive (transitive (+WellDefined reflexive (transitive (transitive (transitive (*WellDefined reflexive (transitive (+WellDefined (transitive groupIsAbelian (+WellDefined (inducedFunctionMult bs c a) (inducedFunctionMult cs b a))) (transitive (transitive (*WellDefined reflexive (transitive (inducedFunctionRingHom bs cs a) *Commutative)) *Associative) *Commutative)) (symmetric +Associative))) *DistributesOver+) (+WellDefined reflexive *DistributesOver+)) (+WellDefined *Associative (+WellDefined (transitive *Associative *Commutative) *Associative)))) +Associative) (+WellDefined (symmetric *DistributesOver+') (symmetric *DistributesOver+'))) (symmetric *DistributesOver+)))

inducedFunctionIsHom : (a : A) → RingHom polyRing R (λ p → inducedFunction p a)
RingHom.preserves1 (inducedFunctionIsHom a) = transitive (+WellDefined reflexive (timesZero {a})) identRight
RingHom.ringHom (inducedFunctionIsHom a) {r} {s} = inducedFunctionRingHom r s a
GroupHom.groupHom (RingHom.groupHom (inducedFunctionIsHom a)) {x} {y} = inducedFunctionGroupHom {x} {y} a
GroupHom.wellDefined (RingHom.groupHom (inducedFunctionIsHom a)) x=y = inducedFunctionWellDefined x=y a
