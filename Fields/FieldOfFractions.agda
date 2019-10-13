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

module Fields.FieldOfFractions where
  fieldOfFractionsSet : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} → {R : Ring S _+_ _*_} → IntegralDomain R → Set (a ⊔ b)
  fieldOfFractionsSet {A = A} {S = S} {R = R} I = (A && (Sg A (λ a → (Setoid._∼_ S a (Ring.0R R) → False))))

  fieldOfFractionsSetoid : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} → {R : Ring S _+_ _*_} → (I : IntegralDomain R) → Setoid (fieldOfFractionsSet I)
  Setoid._∼_ (fieldOfFractionsSetoid {S = S} {_*_ = _*_} I) (a ,, (b , b!=0)) (c ,, (d , d!=0)) = Setoid._∼_ S (a * d) (b * c)
  Equivalence.reflexive (Setoid.eq (fieldOfFractionsSetoid {R = R} I)) {a ,, (b , b!=0)} = Ring.*Commutative R
  Equivalence.symmetric (Setoid.eq (fieldOfFractionsSetoid {S = S} {R = R} I)) {a ,, (b , b!=0)} {c ,, (d , d!=0)} ad=bc = transitive (Ring.*Commutative R) (transitive (symmetric ad=bc) (Ring.*Commutative R))
    where
      open Equivalence (Setoid.eq S)
  Equivalence.transitive (Setoid.eq (fieldOfFractionsSetoid {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} ad=bc cf=de = p5
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
      p4 : (d ∼ 0R) || ((a * f) ∼ (b * e))
      p4 = cancelIntDom I (transitive *Commutative (transitive p3 *Commutative))
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
  Group.+WellDefined (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} {g ,, (h , h!=0)} af=be ch=dg = need
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
  Group.0G (Ring.additiveGroup (fieldOfFractionsRing {R = R} I)) = Ring.0R R ,, (Ring.1R R , IntegralDomain.nontrivial I)
  Group.inverse (Ring.additiveGroup (fieldOfFractionsRing {R = R} I)) (a ,, b) = Group.inverse (Ring.additiveGroup R) a ,, b
  Group.+Associative (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , b!=0)} {c ,, (d , d!=0)} {e ,, (f , f!=0)} = need
    where
      open Setoid S
      open Equivalence eq
      need : (((a * (d * f)) + (b * ((c * f) + (d * e)))) * ((b * d) * f)) ∼ ((b * (d * f)) * ((((a * d) + (b * c)) * f) + ((b * d) * e)))
      need = transitive (Ring.*Commutative R) (Ring.*WellDefined R (symmetric (Ring.*Associative R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Ring.*DistributesOver+ R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Associative R) (Ring.*Associative R))) (transitive (Group.+Associative (Ring.additiveGroup R)) (Group.+WellDefined (Ring.additiveGroup R) (transitive (transitive (Group.+WellDefined (Ring.additiveGroup R) (transitive (Ring.*Associative R) (Ring.*Commutative R)) (Ring.*Commutative R)) (symmetric (Ring.*DistributesOver+ R))) (Ring.*Commutative R)) reflexive)))))
  Group.identRight (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , b!=0)} = need
    where
      open Setoid S
      open Equivalence eq
      need : (((a * Ring.1R R) + (b * Group.0G (Ring.additiveGroup R))) * b) ∼ ((b * Ring.1R R) * a)
      need = transitive (transitive (Ring.*WellDefined R (transitive (Group.+WellDefined (Ring.additiveGroup R) (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) reflexive) (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Ring.timesZero R)) (Group.identRight (Ring.additiveGroup R)))) reflexive) (Ring.*Commutative R)) (symmetric (Ring.*WellDefined R (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) reflexive))
  Group.identLeft (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , _)} = need
    where
      open Setoid S
      open Equivalence eq
      need : (((Group.0G (Ring.additiveGroup R) * b) + (Ring.1R R * a)) * b) ∼ ((Ring.1R R * b) * a)
      need = transitive (transitive (Ring.*WellDefined R (transitive (Group.+WellDefined (Ring.additiveGroup R) reflexive (Ring.identIsIdent R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) (transitive (Ring.*Commutative R) (Ring.timesZero R)) reflexive) (Group.identLeft (Ring.additiveGroup R)))) reflexive) (Ring.*Commutative R)) (Ring.*WellDefined R (symmetric (Ring.identIsIdent R)) reflexive)
  Group.invLeft (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , _)} = need
    where
      open Setoid S
      open Equivalence eq
      need : (((Group.inverse (Ring.additiveGroup R) a * b) + (b * a)) * Ring.1R R) ∼ ((b * b) * Group.0G (Ring.additiveGroup R))
      need = transitive (transitive (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Commutative R) reflexive) (transitive (symmetric (Ring.*DistributesOver+ R)) (transitive (Ring.*WellDefined R reflexive (Group.invLeft (Ring.additiveGroup R))) (Ring.timesZero R))))) (symmetric (Ring.timesZero R))
  Group.invRight (Ring.additiveGroup (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {a ,, (b , _)} = need
    where
      open Setoid S
      open Equivalence eq
      need : (((a * b) + (b * Group.inverse (Ring.additiveGroup R) a)) * Ring.1R R) ∼ ((b * b) * Group.0G (Ring.additiveGroup R))
      need = transitive (transitive (transitive (Ring.*Commutative R) (Ring.identIsIdent R)) (transitive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Commutative R) reflexive) (transitive (symmetric (Ring.*DistributesOver+ R)) (transitive (Ring.*WellDefined R reflexive (Group.invRight (Ring.additiveGroup R))) (Ring.timesZero R))))) (symmetric (Ring.timesZero R))
  Ring.*WellDefined (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} {g ,, (h , _)} af=be ch=dg = need
    where
      open Setoid S
      open Equivalence eq
      need : ((a * c) * (f * h)) ∼ ((b * d) * (e * g))
      need = transitive (Ring.*WellDefined R reflexive (Ring.*Commutative R)) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (symmetric (Ring.*Associative R)) reflexive) (transitive (Ring.*WellDefined R (Ring.*WellDefined R reflexive ch=dg) reflexive) (transitive (Ring.*Commutative R) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (Ring.*Commutative R) reflexive) (transitive (Ring.*WellDefined R af=be reflexive) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (transitive (symmetric (Ring.*Associative R)) (transitive (Ring.*WellDefined R reflexive (Ring.*Commutative R)) (Ring.*Associative R))) reflexive) (symmetric (Ring.*Associative R)))))))))))
  Ring.1R (fieldOfFractionsRing {R = R} I) = Ring.1R R ,, (Ring.1R R , IntegralDomain.nontrivial I)
  Ring.groupIsAbelian (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} = need
    where
      open Setoid S
      open Equivalence eq
      need : (((a * d) + (b * c)) * (d * b)) ∼ ((b * d) * ((c * b) + (d * a)))
      need = transitive (Ring.*Commutative R) (Ring.*WellDefined R (Ring.*Commutative R) (transitive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Commutative R) (Ring.*Commutative R)) (Ring.groupIsAbelian R)))
  Ring.*Associative (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} = need
    where
      open Setoid S
      open Equivalence eq
      need : ((a * (c * e)) * ((b * d) * f)) ∼ ((b * (d * f)) * ((a * c) * e))
      need = transitive (Ring.*WellDefined R (Ring.*Associative R) (symmetric (Ring.*Associative R))) (Ring.*Commutative R)
  Ring.*Commutative (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} = need
    where
      open Setoid S
      open Equivalence eq
      need : ((a * c) * (d * b)) ∼ ((b * d) * (c * a))
      need = transitive (Ring.*Commutative R) (Ring.*WellDefined R (Ring.*Commutative R) (Ring.*Commutative R))
  Ring.*DistributesOver+ (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} = need
    where
      open Setoid S
      open Ring R
      open Equivalence eq
      inter : b * (a * ((c * f) + (d * e))) ∼ (((a * c) * (b * f)) + ((b * d) * (a * e)))
      inter = transitive *Associative (transitive *DistributesOver+ (Group.+WellDefined additiveGroup (transitive *Associative (transitive (*WellDefined (transitive (*WellDefined (*Commutative) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative))) reflexive) (symmetric *Associative))) (transitive *Associative (transitive (*WellDefined (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) reflexive) (symmetric *Associative)))))
      need : ((a * ((c * f) + (d * e))) * ((b * d) * (b * f))) ∼ ((b * (d * f)) * (((a * c) * (b * f)) + ((b * d) * (a * e))))
      need = transitive (Ring.*WellDefined R reflexive (Ring.*WellDefined R reflexive (Ring.*Commutative R))) (transitive (Ring.*WellDefined R reflexive (Ring.*Associative R)) (transitive (Ring.*Commutative R) (transitive (Ring.*WellDefined R (Ring.*WellDefined R (symmetric (Ring.*Associative R)) reflexive) reflexive) (transitive (symmetric (Ring.*Associative R)) (Ring.*WellDefined R reflexive inter)))))
  Ring.identIsIdent (fieldOfFractionsRing {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) {a ,, (b , _)} = need
    where
      open Setoid S
      open Equivalence eq
      need : (((Ring.1R R) * a) * b) ∼ (((Ring.1R R * b)) * a)
      need = transitive (Ring.*WellDefined R (Ring.identIsIdent R) reflexive) (transitive (Ring.*Commutative R) (Ring.*WellDefined R (symmetric (Ring.identIsIdent R)) reflexive))

  fieldOfFractions : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} → (I : IntegralDomain R) → Field (fieldOfFractionsRing I)
  Field.allInvertible (fieldOfFractions {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) (fst ,, (b , _)) prA = (b ,, (fst , ans)) , need
    where
      open Setoid S
      open Equivalence eq
      need : ((b * fst) * Ring.1R R) ∼ ((fst * b) * Ring.1R R)
      need = Ring.*WellDefined R (Ring.*Commutative R) reflexive
      ans : fst ∼ Ring.0R R → False
      ans pr = prA need'
        where
          need' : (fst * Ring.1R R) ∼ (b * Ring.0R R)
          need' = transitive (Ring.*WellDefined R pr reflexive) (transitive (transitive (Ring.*Commutative R) (Ring.timesZero R)) (symmetric (Ring.timesZero R)))
  Field.nontrivial (fieldOfFractions {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I) pr = IntegralDomain.nontrivial I (symmetric (transitive (symmetric (Ring.timesZero R)) (transitive (Ring.*Commutative R) (transitive pr (Ring.identIsIdent R)))))
    where
      open Setoid S
      open Equivalence eq
      pr' : (Ring.0R R) * (Ring.1R R) ∼ (Ring.1R R) * (Ring.1R R)
      pr' = pr

  embedIntoFieldOfFractions : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) → A → fieldOfFractionsSet I
  embedIntoFieldOfFractions {R = R} I a = a ,, (Ring.1R R , IntegralDomain.nontrivial I)

  homIntoFieldOfFractions : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) → RingHom R (fieldOfFractionsRing I) (embedIntoFieldOfFractions I)
  RingHom.preserves1 (homIntoFieldOfFractions {S = S} I) = Equivalence.reflexive (Setoid.eq S)
  RingHom.ringHom (homIntoFieldOfFractions {S = S} {R = R} I) {a} {b} = Equivalence.transitive (Setoid.eq S) (Ring.*WellDefined R (Equivalence.reflexive (Setoid.eq S)) (Ring.identIsIdent R)) (Ring.*Commutative R)
  GroupHom.groupHom (RingHom.groupHom (homIntoFieldOfFractions {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I)) {x} {y} = need
    where
      open Setoid S
      open Equivalence eq
      need : ((x + y) * (Ring.1R R * Ring.1R R)) ∼ (Ring.1R R * ((x * Ring.1R R) + (Ring.1R R * y)))
      need = transitive (transitive (Ring.*WellDefined R reflexive (Ring.identIsIdent R)) (transitive (Ring.*Commutative R) (transitive (Ring.identIsIdent R) (Group.+WellDefined (Ring.additiveGroup R) (symmetric (transitive (Ring.*Commutative R) (Ring.identIsIdent R))) (symmetric (Ring.identIsIdent R)))))) (symmetric (Ring.identIsIdent R))
  GroupHom.wellDefined (RingHom.groupHom (homIntoFieldOfFractions {S = S} {R = R} I)) x=y = transitive (Ring.*Commutative R) (Ring.*WellDefined R reflexive x=y)
    where
      open Equivalence (Setoid.eq S)

  homIntoFieldOfFractionsIsInj : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) → SetoidInjection S (fieldOfFractionsSetoid I) (embedIntoFieldOfFractions I)
  SetoidInjection.wellDefined (homIntoFieldOfFractionsIsInj {S = S} {R = R} I) x=y = transitive (Ring.*Commutative R) (Ring.*WellDefined R reflexive x=y)
    where
      open Equivalence (Setoid.eq S)
  SetoidInjection.injective (homIntoFieldOfFractionsIsInj {S = S} {R = R} I) x~y = transitive (symmetric identIsIdent) (transitive *Commutative (transitive x~y identIsIdent))
    where
      open Ring R
      open Setoid S
      open Equivalence eq
