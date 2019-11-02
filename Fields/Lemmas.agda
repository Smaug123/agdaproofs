{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Groups
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals

module Fields.Lemmas {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) where

open Setoid S
open Field F
open Ring R
open Group additiveGroup

halve : (charNot2 : ((1R + 1R) ∼ 0R) → False) → (a : A) → Sg A (λ i → i + i ∼ a)
halve charNot2 a with allInvertible (1R + 1R) charNot2
... | 1/2 , pr1/2 = (a * 1/2) , Equivalence.transitive eq (+WellDefined *Commutative *Commutative) (Equivalence.transitive eq (Equivalence.symmetric eq (*DistributesOver+ {1/2} {a} {a})) (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) r) (Equivalence.transitive eq (*Associative) (Equivalence.transitive eq (*WellDefined pr1/2 (Equivalence.reflexive eq)) identIsIdent))))
  where
    r : a + a ∼ (1R + 1R) * a
    r = Equivalence.symmetric eq (Equivalence.transitive eq *Commutative (Equivalence.transitive eq *DistributesOver+ (+WellDefined (Equivalence.transitive eq *Commutative identIsIdent) (Equivalence.transitive eq *Commutative identIsIdent))))

abstract

  halfHalves : {x : A} (1/2 : A) (pr : 1/2 + 1/2 ∼ 1R) → (x + x) * 1/2 ∼ x
  halfHalves {x} 1/2 pr = Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq *Commutative (Equivalence.transitive eq (Equivalence.transitive eq *DistributesOver+ (Equivalence.transitive eq (+WellDefined *Commutative *Commutative) (Equivalence.symmetric eq *DistributesOver+))) *Commutative)) (*WellDefined pr (Equivalence.reflexive eq))) identIsIdent
