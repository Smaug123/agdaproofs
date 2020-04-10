{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Modules.Definition
open import Vectors
open import Sets.EquivalenceRelations
open import Sets.FinSet.Definition
open import Modules.Span
open import Groups.Definition

module Modules.VectorModule {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Definition
open import Rings.Lemmas R
open import Groups.Vector (Ring.additiveGroup R)
open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq

ringModule : {n : ℕ} → Module R (abelianVectorGroup {n = n} abelianUnderlyingGroup) λ a v → vecMap (_* a) v
Module.dotWellDefined (ringModule) {r} {s} {[]} {[]} r=s t=u = record {}
Module.dotWellDefined (ringModule) {r} {s} {t ,- ts} {u ,- us} r=s (t=u ,, ts=us) = Ring.*WellDefined R t=u r=s ,, Module.dotWellDefined (ringModule) {r} {s} {ts} {us} r=s ts=us
Module.dotDistributesLeft (ringModule) {a} {[]} {[]} = record {}
Module.dotDistributesLeft (ringModule) {a} {y ,- ys} {z ,- zs} = Ring.*DistributesOver+' R ,, Module.dotDistributesLeft (ringModule) {a} {ys} {zs}
Module.dotDistributesRight (ringModule) {a} {b} {[]} = record {}
Module.dotDistributesRight (ringModule) {a} {b} {z ,- zs} = Ring.*DistributesOver+ R ,, Module.dotDistributesRight (ringModule) {a} {b} {zs}
Module.dotAssociative (ringModule) {r} {s} {[]} = record {}
Module.dotAssociative (ringModule) {r} {s} {x ,- xs} = transitive (Ring.*WellDefined R reflexive (Ring.*Commutative R)) (Ring.*Associative R) ,, Module.dotAssociative (ringModule) {r} {s} {xs}
Module.dotIdentity (ringModule) {[]} = record {}
Module.dotIdentity (ringModule) {x ,- xs} = transitive (Ring.*Commutative R) (Ring.identIsIdent R) ,, Module.dotIdentity ringModule {xs}

vecModuleBasis : {n : ℕ} → FinSet n → Vec A n
vecModuleBasis {succ n} fzero = (Ring.1R R) ,- vecPure (Ring.0R R)
vecModuleBasis {succ n} (fsucc i) = (Ring.0R R) ,- vecModuleBasis i

vecTimesZero : {n : ℕ} (a : A) → vecEquiv {n} (vecMap (_* a) (vecPure 0G)) (vecPure 0G)
vecTimesZero {zero} a = record {}
vecTimesZero {succ n} a = transitive *Commutative timesZero ,, vecTimesZero a

--private
--  lemma2 : {n : ℕ} → (f : _ → _) → (j : _) → vecEquiv (dot ringModule (vecMap (λ i → 0G ,- f i)) j) ?
--  lemma2 = ?

allEntries : (n : ℕ) → Vec (FinSet n) n
allEntries zero = []
allEntries (succ n) = fzero ,- vecMap fsucc (allEntries n)

extractZero : {n m : ℕ} → (y : Vec A m) (xs : Vec (FinSet n) m) (f : FinSet n → Vec A n) → vecEquiv (dot ringModule (vecMap (λ i → 0G ,- f i) xs) y) (0G ,- dot ringModule (vecMap f xs) y)
extractZero {zero} {zero} [] [] f = Equivalence.reflexive (Setoid.eq (vectorSetoid _))
extractZero {zero} {succ m} (y ,- ys) (() ,- xs) f
extractZero {succ n} {zero} [] [] f = reflexive ,, (reflexive ,, Equivalence.reflexive (Setoid.eq (vectorSetoid _)))
extractZero {succ n} {succ m} (y ,- ys) (x ,- xs) f = Equivalence.transitive (Setoid.eq (vectorSetoid _)) (Group.+WellDefined vectorGroup (transitive *Commutative timesZero ,, Equivalence.reflexive (Setoid.eq (vectorSetoid _))) (extractZero ys xs f)) (identLeft ,, Equivalence.reflexive (Setoid.eq (vectorSetoid _)))

identityMatrixProduct : {n : ℕ} → (b : Vec A n) → vecEquiv (dot ringModule (vecMap vecModuleBasis (allEntries n)) b) b
identityMatrixProduct [] = record {}
identityMatrixProduct {succ n} (x ,- b) rewrite vecMapCompose fsucc vecModuleBasis (allEntries n) = Equivalence.transitive (Setoid.eq (vectorSetoid _)) (Group.+WellDefined vectorGroup (identIsIdent ,, vecTimesZero x) (extractZero b (allEntries n) vecModuleBasis)) (identRight ,, Equivalence.transitive (Setoid.eq (vectorSetoid _)) (Group.identLeft vectorGroup) (identityMatrixProduct b))

rearrangeBasis : {n : ℕ} → (coeffs : Vec A n) → (r : Vec (FinSet (succ n)) n) → (eq : vecEquiv (dot ringModule (vecMap vecModuleBasis r) coeffs) (vecPure 0G)) → (uniq : {a : ℕ} {b : ℕ} (a<n : a <N n) (b<n : b <N n) → vecIndex r a a<n ≡ vecIndex r b b<n → a ≡ b) → {!!}
rearrangeBasis coeffs r eq uniq = {!!}


vecModuleBasisSpans : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) {n : ℕ} → Spans (ringModule {n}) (vecModuleBasis {n})
vecModuleBasisSpans R {n} m = n , ((allEntries n ,, m) , identityMatrixProduct m)

vecModuleBasisIndependent : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) {n : ℕ} → Independent (ringModule {n}) (vecModuleBasis {n})
vecModuleBasisIndependent R {zero} [] _ [] x = record {}
vecModuleBasisIndependent R {succ n} r _ [] x = record {}
vecModuleBasisIndependent R {succ n} r uniq coeffs x = {!!}
