{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Rings.Lemmas
open import Rings.IntegralDomains
open import Fields.Fields
open import Functions
open import Setoids.Setoids
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.FieldOfFractions.Addition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Setoid I

fieldOfFractionsPlus : fieldOfFractionsSet → fieldOfFractionsSet → fieldOfFractionsSet
fieldOfFractionsPlus (a ,, (b , b!=0)) (c ,, (d , d!=0)) = (((a * d) + (b * c)) ,, ((b * d) , ans))
  where
    open Setoid S
    open Ring R
    ans : ((b * d) ∼ Ring.0R R) → False
    ans pr with IntegralDomain.intDom I pr
    ans pr | inl x = b!=0 x
    ans pr | inr x = d!=0 x

plusWellDefined : {a b c d : fieldOfFractionsSet} → (Setoid._∼_ fieldOfFractionsSetoid a c) → (Setoid._∼_ fieldOfFractionsSetoid b d) → Setoid._∼_ fieldOfFractionsSetoid (fieldOfFractionsPlus a b) (fieldOfFractionsPlus c d)
plusWellDefined {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} {g ,, (h , h!=0)} af=be ch=dg = need
  where
    open Setoid S
    open Ring R
    open Equivalence eq
    have1 : (c * h) ∼ (d * g)
    have1 = ch=dg
    have2 : (a * f) ∼ (b * e)
    have2 = af=be
    need : (((a * d) + (b * c)) * (f * h)) ∼ ((b * d) * (((e * h) + (f * g))))
    need = transitive (transitive (Ring.*Commutative R) (transitive (Ring.*DistributesOver+ R) (Group.+WellDefined (Ring.additiveGroup R) (transitive *Associative (transitive (*WellDefined (*Commutative) reflexive) (transitive (*WellDefined *Associative reflexive) (transitive (*WellDefined (*WellDefined have2 reflexive) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined (transitive (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative)) *Associative) reflexive) (symmetric *Associative))))))))) (transitive *Commutative (transitive (transitive (symmetric *Associative) (*WellDefined reflexive (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (transitive (*WellDefined have1 reflexive) (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative))))))) *Associative))))) (symmetric (Ring.*DistributesOver+ R))