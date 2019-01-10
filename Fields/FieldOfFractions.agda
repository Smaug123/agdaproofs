{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.GroupsLemmas
open import Rings.RingDefinition
open import Rings.RingLemmas
open import Rings.IntegralDomains
open import Fields.Fields
open import Functions
open import Setoids.Setoids
open import Setoids.Orders

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.FieldOfFractions where
  fieldOfFractionsSet : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} → {R : Ring S _+_ _*_} → IntegralDomain R → Set (a ⊔ b)
  fieldOfFractionsSet {A = A} {S = S} {R = R} I = (A && (Sg A (λ a → (Setoid._∼_ S a (Ring.0R R) → False))))

  fieldOfFractionsSetoid : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} → {R : Ring S _+_ _*_} → (I : IntegralDomain R) → Setoid (fieldOfFractionsSet I)
  Setoid._∼_ (fieldOfFractionsSetoid {S = S} {_*_ = _*_} I) (a ,, (b , b!=0)) (c ,, (d , d!=0)) = Setoid._∼_ S (a * d) (b * c)
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (fieldOfFractionsSetoid {R = R} I))) {a ,, (b , b!=0)} = Ring.multCommutative R
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (fieldOfFractionsSetoid {S = S} {R = R} I))) {a ,, (b , b!=0)} {c ,, (d , d!=0)} ad=bc = transitive (Ring.multCommutative R) (transitive (symmetric ad=bc) (Ring.multCommutative R))
    where
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (fieldOfFractionsSetoid {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I))) {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} ad=bc cf=de = p5
    where
      open Setoid S
      open Ring R
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      p : (a * d) * f ∼ (b * c) * f
      p = Ring.multWellDefined R ad=bc reflexive
      p2 : (a * f) * d ∼ b * (d * e)
      p2 = transitive (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) (transitive p (transitive (symmetric multAssoc) (multWellDefined reflexive cf=de)))
      p3 : (a * f) * d ∼ (b * e) * d
      p3 = transitive p2 (transitive (multWellDefined reflexive multCommutative) multAssoc)
      p4 : (d ∼ 0R) || ((a * f) ∼ (b * e))
      p4 = cancelIntDom I (transitive multCommutative (transitive p3 multCommutative))
      p5 : (a * f) ∼ (b * e)
      p5 with p4
      p5 | inl d=0 = exFalso (d!=0 d=0)
      p5 | inr x = x

  fieldOfFractionsPlus : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} → (I : IntegralDomain R) → fieldOfFractionsSet I → fieldOfFractionsSet I → fieldOfFractionsSet I
  fieldOfFractionsPlus {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I (a ,, (b , b!=0)) (c ,, (d , d!=0)) = (((a * d) + (b * c)) ,, ((b * d) , ans))
    where
      open Setoid S
      open Ring R
      ans : ((b * d) ∼ Ring.0R R) → False
      ans pr with IntegralDomain.intDom I pr
      ans pr | inl x = b!=0 x
      ans pr | inr x = d!=0 x

  fieldOfFractionsTimes : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} → (I : IntegralDomain R) → fieldOfFractionsSet I → fieldOfFractionsSet I → fieldOfFractionsSet I
  fieldOfFractionsTimes {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I (a ,, (b , b!=0)) (c ,, (d , d!=0)) = (a * c) ,, ((b * d) , ans)
    where
      open Setoid S
      open Ring R
      ans : ((b * d) ∼ Ring.0R R) → False
      ans pr with IntegralDomain.intDom I pr
      ans pr | inl x = b!=0 x
      ans pr | inr x = d!=0 x

  fieldOfFractionsRing : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} → (I : IntegralDomain R) → Ring (fieldOfFractionsSetoid I) (fieldOfFractionsPlus I) (fieldOfFractionsTimes I)
  Group.wellDefined (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} {g ,, (h , h!=0)} af=be ch=dg = need
    where
      open Setoid S
      open Ring R
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      have1 : (c * h) ∼ (d * g)
      have1 = ch=dg
      have2 : (a * f) ∼ (b * e)
      have2 = af=be
      need : (((a * d) + (b * c)) * (f * h)) ∼ ((b * d) * (((e * h) + (f * g))))
      need = transitive (transitive (Ring.multCommutative R) (transitive (Ring.multDistributes R) (Group.wellDefined (Ring.additiveGroup R) (transitive multAssoc (transitive (multWellDefined (multCommutative) reflexive) (transitive (multWellDefined multAssoc reflexive) (transitive (multWellDefined (multWellDefined have2 reflexive) reflexive) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined (transitive (transitive (symmetric multAssoc) (multWellDefined reflexive multCommutative)) multAssoc) reflexive) (symmetric multAssoc))))))))) (transitive multCommutative (transitive (transitive (symmetric multAssoc) (multWellDefined reflexive (transitive (multWellDefined reflexive multCommutative) (transitive multAssoc (transitive (multWellDefined have1 reflexive) (transitive (symmetric multAssoc) (multWellDefined reflexive multCommutative))))))) multAssoc))))) (symmetric (Ring.multDistributes R))
  Group.identity (Ring.additiveGroup (fieldOfFractionsRing {R = R} I)) = Ring.0R R ,, (Ring.1R R , IntegralDomain.nontrivial I)
  Group.inverse (Ring.additiveGroup (fieldOfFractionsRing {R = R} I)) (a ,, b) = Group.inverse (Ring.additiveGroup R) a ,, b
  Group.multAssoc (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : (((a * (d * f)) + (b * ((c * f) + (d * e)))) * ((b * d) * f)) ∼ ((b * (d * f)) * ((((a * d) + (b * c)) * f) + ((b * d) * e)))
      need = transitive (Ring.multCommutative R) (Ring.multWellDefined R (symmetric (Ring.multAssoc R)) (transitive (Group.wellDefined (Ring.additiveGroup R) reflexive (Ring.multDistributes R)) (transitive (Group.wellDefined (Ring.additiveGroup R) reflexive (Group.wellDefined (Ring.additiveGroup R) (Ring.multAssoc R) (Ring.multAssoc R))) (transitive (Group.multAssoc (Ring.additiveGroup R)) (Group.wellDefined (Ring.additiveGroup R) (transitive (transitive (Group.wellDefined (Ring.additiveGroup R) (transitive (Ring.multAssoc R) (Ring.multCommutative R)) (Ring.multCommutative R)) (symmetric (Ring.multDistributes R))) (Ring.multCommutative R)) reflexive)))))
  Group.multIdentRight (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , b!=0)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : (((a * Ring.1R R) + (b * Group.identity (Ring.additiveGroup R))) * b) ∼ ((b * Ring.1R R) * a)
      need = transitive (transitive (Ring.multWellDefined R (transitive (Group.wellDefined (Ring.additiveGroup R) (transitive (Ring.multCommutative R) (Ring.multIdentIsIdent R)) reflexive) (transitive (Group.wellDefined (Ring.additiveGroup R) reflexive (ringTimesZero R)) (Group.multIdentRight (Ring.additiveGroup R)))) reflexive) (Ring.multCommutative R)) (symmetric (Ring.multWellDefined R (transitive (Ring.multCommutative R) (Ring.multIdentIsIdent R)) reflexive))
  Group.multIdentLeft (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , _)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : (((Group.identity (Ring.additiveGroup R) * b) + (Ring.1R R * a)) * b) ∼ ((Ring.1R R * b) * a)
      need = transitive (transitive (Ring.multWellDefined R (transitive (Group.wellDefined (Ring.additiveGroup R) reflexive (Ring.multIdentIsIdent R)) (transitive (Group.wellDefined (Ring.additiveGroup R) (transitive (Ring.multCommutative R) (ringTimesZero R)) reflexive) (Group.multIdentLeft (Ring.additiveGroup R)))) reflexive) (Ring.multCommutative R)) (Ring.multWellDefined R (symmetric (Ring.multIdentIsIdent R)) reflexive)
  Group.invLeft (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , _)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : (((Group.inverse (Ring.additiveGroup R) a * b) + (b * a)) * Ring.1R R) ∼ ((b * b) * Group.identity (Ring.additiveGroup R))
      need = transitive (transitive (transitive (Ring.multCommutative R) (Ring.multIdentIsIdent R)) (transitive (Group.wellDefined (Ring.additiveGroup R) (Ring.multCommutative R) reflexive) (transitive (symmetric (Ring.multDistributes R)) (transitive (Ring.multWellDefined R reflexive (Group.invLeft (Ring.additiveGroup R))) (ringTimesZero R))))) (symmetric (ringTimesZero R))
  Group.invRight (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , _)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : (((a * b) + (b * Group.inverse (Ring.additiveGroup R) a)) * Ring.1R R) ∼ ((b * b) * Group.identity (Ring.additiveGroup R))
      need = transitive (transitive (transitive (Ring.multCommutative R) (Ring.multIdentIsIdent R)) (transitive (Group.wellDefined (Ring.additiveGroup R) (Ring.multCommutative R) reflexive) (transitive (symmetric (Ring.multDistributes R)) (transitive (Ring.multWellDefined R reflexive (Group.invRight (Ring.additiveGroup R))) (ringTimesZero R))))) (symmetric (ringTimesZero R))
  Ring.multWellDefined (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} {g ,, (h , _)} af=be ch=dg = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : ((a * c) * (f * h)) ∼ ((b * d) * (e * g))
      need = transitive (Ring.multWellDefined R reflexive (Ring.multCommutative R)) (transitive (Ring.multAssoc R) (transitive (Ring.multWellDefined R (symmetric (Ring.multAssoc R)) reflexive) (transitive (Ring.multWellDefined R (Ring.multWellDefined R reflexive ch=dg) reflexive) (transitive (Ring.multCommutative R) (transitive (Ring.multAssoc R) (transitive (Ring.multWellDefined R (Ring.multCommutative R) reflexive) (transitive (Ring.multWellDefined R af=be reflexive) (transitive (Ring.multAssoc R) (transitive (Ring.multWellDefined R (transitive (symmetric (Ring.multAssoc R)) (transitive (Ring.multWellDefined R reflexive (Ring.multCommutative R)) (Ring.multAssoc R))) reflexive) (symmetric (Ring.multAssoc R)))))))))))
  Ring.1R (fieldOfFractionsRing {R = R} I) = Ring.1R R ,, (Ring.1R R , IntegralDomain.nontrivial I)
  Ring.groupIsAbelian (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : (((a * d) + (b * c)) * (d * b)) ∼ ((b * d) * ((c * b) + (d * a)))
      need = transitive (Ring.multCommutative R) (Ring.multWellDefined R (Ring.multCommutative R) (transitive (Group.wellDefined (Ring.additiveGroup R) (Ring.multCommutative R) (Ring.multCommutative R)) (Ring.groupIsAbelian R)))
  Ring.multAssoc (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : ((a * (c * e)) * ((b * d) * f)) ∼ ((b * (d * f)) * ((a * c) * e))
      need = transitive (Ring.multWellDefined R (Ring.multAssoc R) (symmetric (Ring.multAssoc R))) (Ring.multCommutative R)
  Ring.multCommutative (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : ((a * c) * (d * b)) ∼ ((b * d) * (c * a))
      need = transitive (Ring.multCommutative R) (Ring.multWellDefined R (Ring.multCommutative R) (Ring.multCommutative R))
  Ring.multDistributes (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} = need
    where
      open Setoid S
      open Ring R
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      inter : b * (a * ((c * f) + (d * e))) ∼ (((a * c) * (b * f)) + ((b * d) * (a * e)))
      inter = transitive multAssoc (transitive multDistributes (Group.wellDefined additiveGroup (transitive multAssoc (transitive (multWellDefined (transitive (multWellDefined (multCommutative) reflexive) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc))) reflexive) (symmetric multAssoc))) (transitive multAssoc (transitive (multWellDefined (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive multCommutative) multAssoc)) reflexive) (symmetric multAssoc)))))
      need : ((a * ((c * f) + (d * e))) * ((b * d) * (b * f))) ∼ ((b * (d * f)) * (((a * c) * (b * f)) + ((b * d) * (a * e))))
      need = transitive (Ring.multWellDefined R reflexive (Ring.multWellDefined R reflexive (Ring.multCommutative R))) (transitive (Ring.multWellDefined R reflexive (Ring.multAssoc R)) (transitive (Ring.multCommutative R) (transitive (Ring.multWellDefined R (Ring.multWellDefined R (symmetric (Ring.multAssoc R)) reflexive) reflexive) (transitive (symmetric (Ring.multAssoc R)) (Ring.multWellDefined R reflexive inter)))))
  Ring.multIdentIsIdent (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : (((Ring.1R R) * a) * b) ∼ (((Ring.1R R * b)) * a)
      need = transitive (Ring.multWellDefined R (Ring.multIdentIsIdent R) reflexive) (transitive (Ring.multCommutative R) (Ring.multWellDefined R (symmetric (Ring.multIdentIsIdent R)) reflexive))

  fieldOfFractions : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} → (I : IntegralDomain R) → Field (fieldOfFractionsRing I)
  Field.allInvertible (fieldOfFractions {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) (fst ,, (b , _)) prA = (b ,, (fst , ans)) , need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : ((b * fst) * Ring.1R R) ∼ ((fst * b) * Ring.1R R)
      need = Ring.multWellDefined R (Ring.multCommutative R) reflexive
      ans : fst ∼ Ring.0R R → False
      ans pr = prA need'
        where
          need' : (fst * Ring.1R R) ∼ (b * Ring.0R R)
          need' = transitive (Ring.multWellDefined R pr reflexive) (transitive (transitive (Ring.multCommutative R) (ringTimesZero R)) (symmetric (ringTimesZero R)))
  Field.nontrivial (fieldOfFractions {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) pr = IntegralDomain.nontrivial I (symmetric (transitive (symmetric (ringTimesZero R)) (transitive (Ring.multCommutative R) (transitive pr (Ring.multIdentIsIdent R)))))
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      pr' : (Ring.0R R) * (Ring.1R R) ∼ (Ring.1R R) * (Ring.1R R)
      pr' = pr

  embedIntoFieldOfFractions : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) → A → fieldOfFractionsSet I
  embedIntoFieldOfFractions {R = R} I a = a ,, (Ring.1R R , IntegralDomain.nontrivial I)

  homIntoFieldOfFractions : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) → RingHom R (fieldOfFractionsRing I) (embedIntoFieldOfFractions I)
  RingHom.preserves1 (homIntoFieldOfFractions {S = S} I) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  RingHom.ringHom (homIntoFieldOfFractions {S = S} {R = R} I) {a} {b} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) (Ring.multWellDefined R (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (Ring.multIdentIsIdent R)) (Ring.multCommutative R)
  GroupHom.groupHom (RingHom.groupHom (homIntoFieldOfFractions {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {x} {y} = need
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      need : ((x + y) * (Ring.1R R * Ring.1R R)) ∼ (Ring.1R R * ((x * Ring.1R R) + (Ring.1R R * y)))
      need = transitive (transitive (Ring.multWellDefined R reflexive (Ring.multIdentIsIdent R)) (transitive (Ring.multCommutative R) (transitive (Ring.multIdentIsIdent R) (Group.wellDefined (Ring.additiveGroup R) (symmetric (transitive (Ring.multCommutative R) (Ring.multIdentIsIdent R))) (symmetric (Ring.multIdentIsIdent R)))))) (symmetric (Ring.multIdentIsIdent R))
  GroupHom.wellDefined (RingHom.groupHom (homIntoFieldOfFractions {S = S} {R = R} I)) x=y = transitive (Ring.multCommutative R) (Ring.multWellDefined R reflexive x=y)
    where
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))

  homIntoFieldOfFractionsIsInj : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) → SetoidInjection S (fieldOfFractionsSetoid I) (embedIntoFieldOfFractions I)
  SetoidInjection.wellDefined (homIntoFieldOfFractionsIsInj {S = S} {R = R} I) x=y = transitive (Ring.multCommutative R) (Ring.multWellDefined R reflexive x=y)
    where
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  SetoidInjection.injective (homIntoFieldOfFractionsIsInj {S = S} {R = R} I) x~y = transitive (symmetric multIdentIsIdent) (transitive multCommutative (transitive x~y multIdentIsIdent))
    where
      open Ring R
      open Setoid S
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  fieldOfFractionsNonnegDenom : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → (a1 : fieldOfFractionsSet I) → Sg (fieldOfFractionsSet I) (λ b1 → (Setoid._∼_ (fieldOfFractionsSetoid I) a1 b1) && ((Ring.0R R) < underlying (_&&_.snd b1)))
  fieldOfFractionsNonnegDenom {R = R} {tOrder = tOrder} I order (num ,, (denom , denom!=0)) with SetoidTotalOrder.totality tOrder (Ring.0R R) denom
  fieldOfFractionsNonnegDenom {R = R} {tOrder = tOrder} I order (num ,, (denom , denom!=0)) | inl (inl 0<denom) = (num ,, (denom , denom!=0)) , ((Ring.multCommutative R) ,, 0<denom)
  fieldOfFractionsNonnegDenom {S = S} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order (num ,, (denom , denom!=0)) | inl (inr denom<0) = ((Group.inverse (Ring.additiveGroup R) num ,, (Group.inverse (Ring.additiveGroup R) denom , λ p → denom!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (transitive (symmetric (Group.invLeft (Ring.additiveGroup R) {denom})) (transitive (Group.wellDefined (Ring.additiveGroup R) p reflexive) (Group.multIdentLeft (Ring.additiveGroup R)))))))) , (transitive (ringMinusExtracts R) (transitive (inverseWellDefined (Ring.additiveGroup R) (Ring.multCommutative R)) (symmetric (ringMinusExtracts R))) ,, ringMinusFlipsOrder' order (SetoidPartialOrder.wellDefined pOrder (symmetric (invInv (Ring.additiveGroup R))) reflexive denom<0))
    where
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Ring R
      open Group additiveGroup
  fieldOfFractionsNonnegDenom {S = S} {R = R} {tOrder = tOrder} I order (num ,, (denom , denom!=0)) | inr 0=denom = exFalso (denom!=0 (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) 0=denom))

  fieldOfFractionsComparison : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → Rel (fieldOfFractionsSet I)
  fieldOfFractionsComparison {_*_ = _*_} {R = R} {_<_ = _<_} {tOrder = tOrder} I oring x y with fieldOfFractionsNonnegDenom I oring x
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} I oring x y | (numA ,, (denomA , _)) , b with fieldOfFractionsNonnegDenom I oring y
  fieldOfFractionsComparison {_*_ = _*_} {R} {_<_} {tOrder = tOrder} I oring x y | (numA ,, (denomA , _)) , prA | (numB ,, (denomB , _)) , prB = (numA * denomB) < (numB * denomA)

  fieldOfFractionsOrder : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → SetoidPartialOrder (fieldOfFractionsSetoid I) (fieldOfFractionsComparison I order)
  SetoidPartialOrder.wellDefined (fieldOfFractionsOrder {S = S} {_+_ = _+_} {_*_ = _*_} {_<_ = _<_} I order) {w} {x} {y} {z} a~b c~d a<c with fieldOfFractionsNonnegDenom I order x
  SetoidPartialOrder.wellDefined (fieldOfFractionsOrder {S = S} {_+_} {_*_} {_<_ = _<_} I order) {w} {x} {y} {z} a~b c~d a<c | (numX ,, (denomX , denomX!=0)) , (x~numX/denomX ,, 0<denomX) with fieldOfFractionsNonnegDenom I order z
  SetoidPartialOrder.wellDefined (fieldOfFractionsOrder {S = S} {_+_} {_*_} {_<_ = _<_} I order) {w} {x} {y} {z} a~b c~d a<c | (numX ,, (denomX , denomX!=0)) , (x~numX/denomX ,, 0<denomX) | (numZ ,, (denomZ , denomZ!=0)) , (numZ/denomZ ,, 0<denomZ) with fieldOfFractionsNonnegDenom I order w
  SetoidPartialOrder.wellDefined (fieldOfFractionsOrder {S = S} {_+_} {_*_} {_<_ = _<_} I order) {w} {x} {y} {z} a~b c~d a<c | (numX ,, (denomX , denomX!=0)) , (x~numX/denomX ,, 0<denomX) | (numZ ,, (denomZ , denomZ!=0)) , (numZ/denomZ ,, 0<denomZ) | (numW ,, (denomW , denomW!=0)) , (numW/denomW ,, 0<denomW) with fieldOfFractionsNonnegDenom I order y
  SetoidPartialOrder.wellDefined (fieldOfFractionsOrder {S = S} {_+_} {_*_} {_<_ = _<_} I order) {numW' ,, (denomW' , denomW'!=0)} {numX' ,, (denomX' , denomX'!=0)} {numY' ,, (denomY' , denomY'!=0)} {numZ' ,, (denomZ' , denomZ'!=0)} a~b c~d a<c | (numX ,, (denomX , denomX!=0)) , (x~numX/denomX ,, 0<denomX) | (numZ ,, (denomZ , denomZ!=0)) , (numZ/denomZ ,, 0<denomZ) | (numW ,, (denomW , denomW!=0)) , (numW/denomW ,, 0<denomW) | (numY ,, (denomY , denomY!=0)) , (numY/denomY ,, 0<denomY) = {!!}

  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {R = R} {pOrder = pOrder} {tOrder = tOrder} I oRing) {x} x<x with fieldOfFractionsNonnegDenom I oRing x
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder} I oRing) {x} x<x | (numA ,, (denomA , _)) , pr with fieldOfFractionsNonnegDenom I oRing x
  SetoidPartialOrder.irreflexive (fieldOfFractionsOrder {S = S} {_*_ = _*_} {R} {_<_} {pOrder} {tOrder} I oRing) {fst₁ ,, (a , a!=0)} x<x | (numA ,, (denomA , _)) , (fst₂ ,, 0<denomA) | (numA' ,, (denomA' , _)) , (fst ,, 0<denomA') = {!!}
  SetoidPartialOrder.transitive (fieldOfFractionsOrder {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {_<_ = _<_} {pOrder = pOrder} {tOrder = tOrder} I order) {numA ,, (denomA , _)} {(numB ,, (denomB , _))} {numC ,, (denomC , _)} a<b b<c = {!!}

  fieldOfFractionsTotalOrder : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → SetoidTotalOrder (fieldOfFractionsOrder I order)
  fieldOfFractionsTotalOrder I order = {!!}

  fieldOfFractionsOrderedRing : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (I : IntegralDomain R) → (order : OrderedRing R tOrder) → OrderedRing (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I order)
  OrderedRing.orderRespectsAddition (fieldOfFractionsOrderedRing I order) a<b c = {!!}
  OrderedRing.orderRespectsMultiplication (fieldOfFractionsOrderedRing {_+_ = _+_} {_*_ = _*_} {_<_ = _<_} I order) {numA ,, (denomA , _)} {numB ,, (denomB , _)} 0<a 0<b = {!!}
