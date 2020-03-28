{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Groups.Definition
open import Groups.Abelian.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Sets.FinSet.Definition
open import Vectors
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Modules.Definition

module Modules.Span {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+R_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+R_ _*_} {m n : _} {M : Set m} {T : Setoid {m} {n} M} {_+_ : M → M → M} {G' : Group T _+_} {G : AbelianGroup G'} {_·_ : A → M → M} (mod : Module R G _·_) where

open Group G'
open Setoid T
open Equivalence eq

_=V_ : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) {n1 : ℕ} → Rel {a} {b ⊔ n} (Vec A n1)
_=V_ G [] [] = True'
_=V_ {S = S} G (x ,- xs) (y ,- ys) = (Setoid._∼_ S x y) && (_=V_ G xs ys)

dot : {n : ℕ} → (Vec M n) → (Vec A n) → M
dot [] [] = 0G
dot (v ,- vs) (x ,- xs) = (x · v) + (dot vs xs)

Spans : {c : _} {C : Set c} (f : C → M) → Set (a ⊔ m ⊔ n ⊔ c)
Spans {C = C} f = (m : M) → Sg ℕ (λ n → Sg ((Vec C n) && (Vec A n)) (λ t → (dot (vecMap f (_&&_.fst t)) (_&&_.snd t)) ∼ m))

Independent : {c : _} {C : Set c} (f : C → M) → Set (a ⊔ b ⊔ n ⊔ c)
Independent {C = C} f = {n : ℕ} → (r : Vec C n) → ({a b : ℕ} → (a<n : a <N n) → (b<n : b <N n) → vecIndex r a a<n ≡ vecIndex r b b<n → a ≡ b) → (b : Vec A n) → (dot (vecMap f r) b) ∼ 0G → _=V_ (Ring.additiveGroup R) (vecPure (Group.0G (Ring.additiveGroup R))) b

independentSubset : {c : _} {C : Set c} (f : C → M) → {d : _} {D : Set d} {inj : D → C} (isInj : Injection inj) → Independent f → Independent (f ∘ inj)
independentSubset f {inj = inj} isInj indp {n = n} r coeffInj coeffs dotZero = indp {n = n} (vecMap inj r) inj' coeffs (transitive (identityOfIndiscernablesRight _∼_ reflexive (applyEquality (λ i → dot i coeffs) (vecMapCompose inj f r))) dotZero)
  where
    inj' : {a b : ℕ} (a<n : a <N n) (b<n : b <N n) → vecIndex (vecMap inj r) a a<n ≡ vecIndex (vecMap inj r) b b<n → a ≡ b
    inj' a<n b<n x rewrite vecMapAndIndex r inj a<n | vecMapAndIndex r inj b<n = coeffInj a<n b<n (isInj x)

spanSuperset : {c : _} {C : Set c} (f : C → M) → {d : _} {D : Set d} {surj : D → C} (isSurj : Surjection surj) → Spans f → Spans (f ∘ surj)
spanSuperset f {surj = surj} isSurj spans m with spans m
spanSuperset {C = C} f {surj = surj} isSurj spans m | n , ((coeffs ,, basis) , b) = n , ((vecMap (λ c → underlying (isSurj c)) coeffs ,, basis) , transitive (identityOfIndiscernablesLeft _∼_ reflexive (applyEquality (λ i → dot i basis) (equalityCommutative {x = vecMap (λ i → f (surj i)) (vecMap (λ c → underlying (isSurj c)) coeffs)} {vecMap f coeffs} (transitivity (vecMapCompose (λ i → underlying (isSurj i)) (λ z → f (surj z)) coeffs) (t coeffs))))) b)
  where
    t : {n : ℕ} (coeffs : Vec C n) → vecMap (λ i → f (surj (underlying (isSurj i)))) coeffs ≡ vecMap f coeffs
    t [] = refl
    t (x ,- coeffs) with isSurj x
    ... | img , pr rewrite pr | t coeffs = refl

Basis : {c : _} {C : Set c} (f : C → M) → Set (a ⊔ b ⊔ m ⊔ n ⊔ c)
Basis v = Spans v && Independent v
