{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Rings.Definition
open import Rings.Order
open import Rings.Lemmas
open import Setoids.Setoids
open import Setoids.Orders
open import Orders
open import Rings.IntegralDomains
open import Functions
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Fields where
  record Field {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) : Set (lsuc m ⊔ n) where
    open Ring R
    open Group additiveGroup
    open Setoid S
    field
      allInvertible : (a : A) → ((a ∼ Group.0G (Ring.additiveGroup R)) → False) → Sg A (λ t → t * a ∼ 1R)
      nontrivial : (0R ∼ 1R) → False

  orderedFieldIsIntDom : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {c} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (O : OrderedRing R tOrder) (F : Field R) → IntegralDomain R
  IntegralDomain.intDom (orderedFieldIsIntDom {S = S} {_*_ = _*_} {R = R} {tOrder = tOrder} O F) {a} {b} ab=0 with SetoidTotalOrder.totality tOrder (Ring.0R R) a
  IntegralDomain.intDom (orderedFieldIsIntDom {A = A} {S = S} {_*_ = _*_} {R = R} {pOrder = pOrder} {tOrder = tOrder} O F) {a} {b} ab=0 | inl (inl x) = inr (transitive (transitive (symmetric identIsIdent) (*WellDefined q reflexive)) p')
    where
      open Setoid S
      open Equivalence eq
      open Ring R
      a!=0 : (a ∼ Group.0G additiveGroup) → False
      a!=0 pr = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder (symmetric pr) reflexive x)
      invA : A
      invA = underlying (Field.allInvertible F a a!=0)
      q : 1R ∼ (invA * a)
      q with Field.allInvertible F a a!=0
      ... | invA , pr = symmetric pr
      p : invA * (a * b) ∼ invA * Group.0G additiveGroup
      p = *WellDefined reflexive ab=0
      p' : (invA * a) * b ∼ Group.0G additiveGroup
      p' = transitive (symmetric *Associative) (transitive p (Ring.timesZero R))
  IntegralDomain.intDom (orderedFieldIsIntDom {A = A} {S = S} {_*_ = _*_} {R = R} {pOrder = pOrder} {tOrder = tOrder} O F) {a} {b} ab=0 | inl (inr x) = inr (transitive (transitive (symmetric identIsIdent) (*WellDefined q reflexive)) p')
    where
      open Setoid S
      open Equivalence eq
      open Ring R
      a!=0 : (a ∼ Group.0G additiveGroup) → False
      a!=0 pr = SetoidPartialOrder.irreflexive pOrder (SetoidPartialOrder.<WellDefined pOrder reflexive (symmetric pr) x)
      invA : A
      invA = underlying (Field.allInvertible F a a!=0)
      q : 1R ∼ (invA * a)
      q with Field.allInvertible F a a!=0
      ... | invA , pr = symmetric pr
      p : invA * (a * b) ∼ invA * Group.0G additiveGroup
      p = *WellDefined reflexive ab=0
      p' : (invA * a) * b ∼ Group.0G additiveGroup
      p' = transitive (symmetric *Associative) (transitive p (Ring.timesZero R))
  IntegralDomain.intDom (orderedFieldIsIntDom {S = S} {_*_ = _*_} {R = R} {tOrder = tOrder} O F) {a} {b} ab=0 | inr x = inl (Equivalence.symmetric (Setoid.eq S) x)
  IntegralDomain.nontrivial (orderedFieldIsIntDom {S = S} O F) pr = Field.nontrivial F (Equivalence.symmetric (Setoid.eq S) pr)

  record Field' {m n : _} : Set (lsuc m ⊔ lsuc n) where
    field
      A : Set m
      S : Setoid {m} {n} A
      _+_ : A → A → A
      _*_ : A → A → A
      R : Ring S _+_ _*_
      isField : Field R

  encapsulateField : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) → Field'
  encapsulateField {A = A} {S = S} {_+_} {_*_} {R} F = record { A = A ; S = S ; _+_ = _+_ ; _*_ = _*_ ; R = R ; isField = F }


{-
  record OrderedField {n} {A : Set n} {R : Ring A} (F : Field R) : Set (lsuc n) where
    open Field F
    field
      ord : TotalOrder A
    open TotalOrder ord
    open Ring R
    field
      productPos : {a b : A} → (0R < a) → (0R < b) → (0R < (a * b))
      orderRespectsAddition : {a b c : A} → (a < b) → (a + c) < (b + c)

-}
