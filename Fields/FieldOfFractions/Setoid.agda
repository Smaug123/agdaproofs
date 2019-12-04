{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Rings.Lemmas
open import Fields.Fields
open import Functions
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.IntegralDomains.Definition
open import Rings.IntegralDomains.Lemmas

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.FieldOfFractions.Setoid {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

fieldOfFractionsSet : Set (a ⊔ b)
fieldOfFractionsSet = (A && (Sg A (λ a → (Setoid._∼_ S a (Ring.0R R) → False))))

fieldOfFractionsSetoid : Setoid fieldOfFractionsSet
Setoid._∼_ fieldOfFractionsSetoid (a ,, (b , b!=0)) (c ,, (d , d!=0)) = Setoid._∼_ S (a * d) (b * c)
Equivalence.reflexive (Setoid.eq fieldOfFractionsSetoid) {a ,, (b , b!=0)} = Ring.*Commutative R
Equivalence.symmetric (Setoid.eq fieldOfFractionsSetoid) {a ,, (b , b!=0)} {c ,, (d , d!=0)} ad=bc = transitive (Ring.*Commutative R) (transitive (symmetric ad=bc) (Ring.*Commutative R))
  where
    open Equivalence (Setoid.eq S)
Equivalence.transitive (Setoid.eq fieldOfFractionsSetoid) {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} ad=bc cf=de = p5
  where
    open Setoid S
    open Ring R
    open Equivalence eq
    p : (a * d) * f ∼ (b * c) * f
    p = Ring.*WellDefined R ad=bc reflexive
    p2 : (a * f) * d ∼ b * (d * e)
    p2 = transitive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive p (transitive (symmetric *Associative) (*WellDefined reflexive cf=de)))
    p3 : (a * f) * d ∼ (b * e) * d
    p3 = transitive p2 (transitive (*WellDefined reflexive *Commutative) *Associative)
    p4 : ((d ∼ 0R) → False) → ((a * f) ∼ (b * e))
    p4 = cancelIntDom R I (transitive *Commutative (transitive p3 *Commutative))
    p5 : (a * f) ∼ (b * e)
    p5 = p4 d!=0
