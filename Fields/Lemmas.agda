{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Rings.Definition
open import Groups.Definition
open import Fields.Fields
open import Sets.EquivalenceRelations
open import LogicalFormulae
open import Rings.IntegralDomains.Definition
open import Rings.IntegralDomains.Lemmas

module Fields.Lemmas {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) where

open Setoid S
open Field F
open Ring R
open Group additiveGroup
open Equivalence eq
open import Rings.Lemmas R

halve : (charNot2 : ((1R + 1R) ∼ 0R) → False) → (a : A) → Sg A (λ i → i + i ∼ a)
halve charNot2 a with allInvertible (1R + 1R) charNot2
... | 1/2 , pr1/2 = (a * 1/2) , transitive (+WellDefined *Commutative *Commutative) (transitive (symmetric (*DistributesOver+ {1/2} {a} {a})) (transitive (*WellDefined (reflexive) r) (transitive (*Associative) (transitive (*WellDefined pr1/2 (reflexive)) identIsIdent))))
  where
    r : a + a ∼ (1R + 1R) * a
    r = symmetric (transitive *Commutative (transitive *DistributesOver+ (+WellDefined (transitive *Commutative identIsIdent) (transitive *Commutative identIsIdent))))

abstract

  halfHalves : {x : A} (1/2 : A) (pr : 1/2 + 1/2 ∼ 1R) → (x + x) * 1/2 ∼ x
  halfHalves {x} 1/2 pr = transitive (transitive (transitive *Commutative (transitive (transitive *DistributesOver+ (transitive (+WellDefined *Commutative *Commutative) (symmetric *DistributesOver+))) *Commutative)) (*WellDefined pr (reflexive))) identIsIdent

fieldIsIntDom : (Setoid._∼_ S (Ring.1R R) (Ring.0R R) → False) → IntegralDomain R
IntegralDomain.intDom (fieldIsIntDom 1!=0) {a} {b} ab=0 a!=0 with Field.allInvertible F a a!=0
IntegralDomain.intDom (fieldIsIntDom _) {a} {b} ab=0 a!=0 | 1/a , prA = transitive (symmetric identIsIdent) (transitive (*WellDefined (symmetric prA) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive ab=0) (Ring.timesZero R))))
IntegralDomain.nontrivial (fieldIsIntDom 1!=0) = 1!=0

allInvertibleWellDefined : {a b : A} {a!=0 : (a ∼ 0F) → False} {b!=0 : (b ∼ 0F) → False} → (a ∼ b) → underlying (allInvertible a a!=0) ∼ underlying (allInvertible b b!=0)
allInvertibleWellDefined {a} {b} {a!=0} {b!=0} a=b with allInvertible a a!=0
... | x , prX with allInvertible b b!=0
... | y , prY with transitive (transitive prX (symmetric prY)) (*WellDefined reflexive (symmetric a=b))
... | xa=ya = cancelIntDom (fieldIsIntDom λ p → a!=0 (oneZeroImpliesAllZero (symmetric p))) (transitive *Commutative (transitive xa=ya *Commutative)) a!=0
