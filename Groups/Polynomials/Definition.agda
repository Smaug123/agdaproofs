{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Lists.Lists
open import Maybe

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Polynomials.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open Setoid S
open Equivalence eq
open Group G

NaivePoly : Set a
NaivePoly = List A

0P : NaivePoly
0P = []

polysEqual : NaivePoly → NaivePoly → Set (a ⊔ b)
polysEqual [] [] = True'
polysEqual [] (x :: b) = (x ∼ 0G) && polysEqual [] b
polysEqual (x :: a) [] = (x ∼ 0G) && polysEqual a []
polysEqual (x :: a) (y :: b) = (x ∼ y) && polysEqual a b

polysReflexive : {x : NaivePoly} → polysEqual x x
polysReflexive {[]} = record {}
polysReflexive {x :: y} = reflexive ,, polysReflexive

polysSymmetricZero : {x : NaivePoly} → polysEqual [] x → polysEqual x []
polysSymmetricZero {[]} 0=x = record {}
polysSymmetricZero {x :: y} (fst ,, snd) = fst ,, polysSymmetricZero snd

polysSymmetricZero' : {x : NaivePoly} → polysEqual x [] → polysEqual [] x
polysSymmetricZero' {[]} 0=x = record {}
polysSymmetricZero' {x :: y} (fst ,, snd) = fst ,, polysSymmetricZero' snd

polysSymmetric : {x y : NaivePoly} → polysEqual x y → polysEqual y x
polysSymmetric {[]} {y} x=y = polysSymmetricZero x=y
polysSymmetric {x :: xs} {[]} x=y = polysSymmetricZero' {x :: xs} x=y
polysSymmetric {x :: xs} {y :: ys} (fst ,, snd) = symmetric fst ,, polysSymmetric {xs} {ys} snd

polysTransitive : {x y z : NaivePoly} → polysEqual x y → polysEqual y z → polysEqual x z
polysTransitive {[]} {[]} {[]} x=y y=z = record {}
polysTransitive {[]} {[]} {x :: z} x=y y=z = y=z
polysTransitive {[]} {x :: y} {[]} (fst ,, snd) y=z = record {}
polysTransitive {[]} {x :: y} {x₁ :: z} (fst ,, snd) (fst2 ,, snd2) = transitive (symmetric fst2) fst ,, polysTransitive snd snd2
polysTransitive {x :: xs} {[]} {[]} x=y y=z = x=y
polysTransitive {x :: xs} {[]} {z :: zs} (fst ,, snd) (fst2 ,, snd2) = transitive fst (symmetric fst2) ,, polysTransitive snd snd2
polysTransitive {x :: xs} {y :: ys} {[]} (fst ,, snd) (fst2 ,, snd2) = transitive fst fst2 ,, polysTransitive snd snd2
polysTransitive {x :: xs} {y :: ys} {z :: zs} (fst ,, snd) (fst2 ,, snd2) = transitive fst fst2 ,, polysTransitive snd snd2

naivePolySetoid : Setoid NaivePoly
Setoid._∼_ naivePolySetoid = polysEqual
Equivalence.reflexive (Setoid.eq naivePolySetoid) = polysReflexive
Equivalence.symmetric (Setoid.eq naivePolySetoid) = polysSymmetric
Equivalence.transitive (Setoid.eq naivePolySetoid) = polysTransitive

polyInjection : A → NaivePoly
polyInjection a = a :: []

polyInjectionIsInj : SetoidInjection S naivePolySetoid polyInjection
SetoidInjection.wellDefined polyInjectionIsInj x=y = x=y ,, record {}
SetoidInjection.injective polyInjectionIsInj {x} {y} (fst ,, snd) = fst

-- the zero polynomial has no degree
-- all other polynomials have a degree

degree : ((x : A) → (x ∼ 0G) || ((x ∼ 0G) → False)) → NaivePoly → Maybe ℕ
degree decide [] = no
degree decide (x :: poly) with decide x
degree decide (x :: poly) | inl x=0 with degree decide poly
degree decide (x :: poly) | inl x=0 | no = no
degree decide (x :: poly) | inl x=0 | yes deg = yes (succ deg)
degree decide (x :: poly) | inr x!=0 with degree decide poly
degree decide (x :: poly) | inr x!=0 | no = yes 0
degree decide (x :: poly) | inr x!=0 | yes n = yes (succ n)

degreeWellDefined : (decide : ((x : A) → (x ∼ 0G) || ((x ∼ 0G) → False))) {x y : NaivePoly} → polysEqual x y → degree decide x ≡ degree decide y
degreeWellDefined decide {[]} {[]} x=y = refl
degreeWellDefined decide {[]} {x :: y} (fst ,, snd) with decide x
degreeWellDefined decide {[]} {x :: y} (fst ,, snd) | inl x=0 with inspect (degree decide y)
degreeWellDefined decide {[]} {x :: y} (fst ,, snd) | inl x=0 | no with≡ pr rewrite pr = refl
degreeWellDefined decide {[]} {x :: y} (fst ,, snd) | inl x=0 | yes bad with≡ pr rewrite pr = exFalso (noNotYes (transitivity (degreeWellDefined decide {[]} {y} snd) pr))
degreeWellDefined decide {[]} {x :: y} (fst ,, snd) | inr x!=0 with inspect (degree decide y)
degreeWellDefined decide {[]} {x :: y} (fst ,, snd) | inr x!=0 | no with≡ pr rewrite pr = exFalso (x!=0 fst)
degreeWellDefined decide {[]} {x :: y} (fst ,, snd) | inr x!=0 | yes deg with≡ pr rewrite pr = exFalso (x!=0 fst)
degreeWellDefined decide {x :: xs} {[]} x=y with decide x
degreeWellDefined decide {x :: xs} {[]} (fst ,, snd) | inl x=0 with inspect (degree decide xs)
degreeWellDefined decide {x :: xs} {[]} (fst ,, snd) | inl x=0 | no with≡ pr rewrite pr = refl
degreeWellDefined decide {x :: xs} {[]} (fst ,, snd) | inl x=0 | yes bad with≡ pr rewrite pr = exFalso (noNotYes (transitivity (equalityCommutative (degreeWellDefined decide snd)) pr))
degreeWellDefined decide {x :: xs} {[]} (fst ,, snd) | inr x!=0 = exFalso (x!=0 fst)
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) with decide x
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inl x=0 with decide y
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inl x=0 | inl y=0 with inspect (degree decide ys)
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inl x=0 | inl y=0 | no with≡ pr rewrite degreeWellDefined decide {xs} {ys} snd | pr = refl
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inl x=0 | inl y=0 | (yes th) with≡ pr rewrite degreeWellDefined decide {xs} {ys} snd | pr = refl
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inl x=0 | inr y!=0 = exFalso (y!=0 (transitive (symmetric fst) x=0))
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inr x!=0 with decide y
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inr x!=0 | inl y=0 = exFalso (x!=0 (transitive fst y=0))
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inr x!=0 | inr y!=0 with inspect (degree decide ys)
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inr x!=0 | inr y!=0 | no with≡ pr rewrite degreeWellDefined decide {xs} {ys} snd | pr = refl
degreeWellDefined decide {x :: xs} {y :: ys} (fst ,, snd) | inr x!=0 | inr y!=0 | yes x₁ with≡ pr rewrite degreeWellDefined decide {xs} {ys} snd | pr = refl

degreeNoImpliesZero : (decide : ((x : A) → (x ∼ 0G) || ((x ∼ 0G) → False))) → (a : NaivePoly) → degree decide a ≡ no → polysEqual a []
degreeNoImpliesZero decide [] not = record {}
degreeNoImpliesZero decide (x :: a) not with decide x
degreeNoImpliesZero decide (x :: a) not | inl x=0 with inspect (degree decide a)
degreeNoImpliesZero decide (x :: a) not | inl x=0 | no with≡ pr rewrite pr = x=0 ,, degreeNoImpliesZero decide a pr
degreeNoImpliesZero decide (x :: a) not | inl x=0 | (yes deg) with≡ pr rewrite pr = exFalso (noNotYes (equalityCommutative not))
degreeNoImpliesZero decide (x :: a) not | inr x!=0 with degree decide a
degreeNoImpliesZero decide (x :: a) () | inr x!=0 | no
degreeNoImpliesZero decide (x :: a) () | inr x!=0 | yes x₁

emptyImpliesDegreeZero : (decide : ((x : A) → (x ∼ 0G) || ((x ∼ 0G) → False))) → (a : NaivePoly) → polysEqual a [] → degree decide a ≡ no
emptyImpliesDegreeZero decide [] a=[] = refl
emptyImpliesDegreeZero decide (x :: a) (fst ,, snd) with decide x
emptyImpliesDegreeZero decide (x :: a) (fst ,, snd) | inl x=0 with inspect (degree decide a)
emptyImpliesDegreeZero decide (x :: a) (fst ,, snd) | inl x=0 | no with≡ pr rewrite pr = refl
emptyImpliesDegreeZero decide (x :: a) (fst ,, snd) | inl x=0 | (yes deg) with≡ pr rewrite pr = exFalso (noNotYes (transitivity (equalityCommutative (emptyImpliesDegreeZero decide a snd)) pr))
emptyImpliesDegreeZero decide (x :: a) (fst ,, snd) | inr x!=0 = exFalso (x!=0 fst)
