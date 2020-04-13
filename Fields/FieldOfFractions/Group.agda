{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations

module Fields.FieldOfFractions.Group {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Setoid I
open import Fields.FieldOfFractions.Addition I

fieldOfFractionsGroup : Group fieldOfFractionsSetoid fieldOfFractionsPlus
Group.+WellDefined fieldOfFractionsGroup {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} {g ,, (h , h!=0)} af=be ch=dg = need
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
Group.0G fieldOfFractionsGroup = Ring.0R R ,, (Ring.1R R , IntegralDomain.nontrivial I)
Group.inverse fieldOfFractionsGroup (a ,, b) = Group.inverse (Ring.additiveGroup R) a ,, b
Group.+Associative fieldOfFractionsGroup {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((a * (d * f)) + (b * ((c * f) + (d * e)))) * ((b * d) * f)) ∼ ((b * (d * f)) * ((((a * d) + (b * c)) * f) + ((b * d) * e)))
    need = transitive (Ring.*Commutative R) (Ring.*WellDefined R (symmetric (Ring.*Associative R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Ring.*DistributesOver+ R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Associative R) (Ring.*Associative R))) (transitive (Group.+Associative (Ring.additiveGroup R)) (Group.+WellDefined (Ring.additiveGroup R) (transitive (transitive (Group.+WellDefined (Ring.additiveGroup R) (transitive (Ring.*Associative R) (Ring.*Commutative R)) (Ring.*Commutative R)) (symmetric (Ring.*DistributesOver+ R))) (Ring.*Commutative R)) reflexive)))))
Group.identRight fieldOfFractionsGroup {a ,, (b , b!=0)} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((a * Ring.1R R) + (b * Group.0G (Ring.additiveGroup R))) * b) ∼ ((b * Ring.1R R) * a)
    need = transitive (transitive (Ring.*WellDefined R (transitive (Group.+WellDefined (Ring.additiveGroup R) (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) reflexive) (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Ring.timesZero R)) (Group.identRight (Ring.additiveGroup R)))) reflexive) (Ring.*Commutative R)) (symmetric (Ring.*WellDefined R (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) reflexive))
Group.identLeft fieldOfFractionsGroup {a ,, (b , _)} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((Group.0G (Ring.additiveGroup R) * b) + (Ring.1R R * a)) * b) ∼ ((Ring.1R R * b) * a)
    need = transitive (transitive (Ring.*WellDefined R (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Ring.identIsIdent R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) (transitive (Ring.*Commutative R) (Ring.timesZero R)) reflexive) (Group.identLeft (Ring.additiveGroup R)))) reflexive) (Ring.*Commutative R)) (Ring.*WellDefined R (symmetric (Ring.identIsIdent R)) reflexive)
Group.invLeft fieldOfFractionsGroup {a ,, (b , _)} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((Group.inverse (Ring.additiveGroup R) a * b) + (b * a)) * Ring.1R R) ∼ ((b * b) * Group.0G (Ring.additiveGroup R))
    need = transitive (transitive (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Commutative R) reflexive) (transitive (symmetric (Ring.*DistributesOver+ R)) (transitive (Ring.*WellDefined R reflexive (Group.invLeft (Ring.additiveGroup R))) (Ring.timesZero R))))) (symmetric (Ring.timesZero R))
Group.invRight fieldOfFractionsGroup {a ,, (b , _)} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((a * b) + (b * Group.inverse (Ring.additiveGroup R) a)) * Ring.1R R) ∼ ((b * b) * Group.0G (Ring.additiveGroup R))
    need = transitive (transitive (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Commutative R) reflexive) (transitive (symmetric (Ring.*DistributesOver+ R)) (transitive (Ring.*WellDefined R reflexive (Group.invRight (Ring.additiveGroup R))) (Ring.timesZero R))))) (symmetric (Ring.timesZero R))
