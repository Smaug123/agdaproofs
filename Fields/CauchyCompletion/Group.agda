{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Groups
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals

module Fields.CauchyCompletion.Group {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open TotallyOrderedRing order
open Field F
open Group (Ring.additiveGroup R)

open import Rings.Orders.Total.Lemmas order
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Addition order F charNot2
open import Fields.CauchyCompletion.Setoid order F charNot2

Cassoc : {a b c : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a +C (b +C c)) ((a +C b) +C c)
Cassoc {a} {b} {c} ε 0<e = 0 , ans
  where
    ans : {m : ℕ} → 0 <N m → abs (index (CauchyCompletion.elts ((a +C (b +C c)) +C (-C ((a +C b) +C c)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a +C (b +C c))) (map inverse (CauchyCompletion.elts ((a +C b) +C c))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (apply _+_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)) _+_ {m} | equalityCommutative (mapAndIndex (apply _+_ (apply _+_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (CauchyCompletion.elts c)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts c) _+_ {m} | indexAndApply (apply _+_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (CauchyCompletion.elts c) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _+_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (transferToRight'' (Ring.additiveGroup R) +Associative)) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

CidentRight : {a : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a +C injection 0G) a
CidentRight {a} ε 0<e = 0 , ans
  where
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (a +C injection 0G)) (map inverse (CauchyCompletion.elts a))) m) < ε
    ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a +C injection 0G)) (map inverse (CauchyCompletion.elts a)) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (constSequence 0G) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) | indexAndConst 0G m = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.transitive eq (+WellDefined (identRight) (Equivalence.reflexive eq)) (invRight))) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

CidentLeft : {a : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (injection 0G +C a) a
CidentLeft {a} = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection 0G +C a} {a +C injection 0G} {a} (+CCommutative {injection 0G} {a}) (CidentRight {a})

CinvRight : {a : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a +C (-C a)) (injection 0G)
CinvRight {a} ε 0<e = 0 , ans
  where
    ans : {m : ℕ} → (0 <N m) → abs (index (apply _+_ (CauchyCompletion.elts (a +C (-C a))) (map inverse (CauchyCompletion.elts (injection 0G)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a +C (-C a))) (map inverse (CauchyCompletion.elts (injection 0G))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts a)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) | equalityCommutative (mapAndIndex (constSequence 0G) inverse m) | indexAndConst 0G m = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.transitive eq (+WellDefined invRight (invIdentity (Ring.additiveGroup R))) identRight)) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

CGroup : Group cauchyCompletionSetoid _+C_
Group.+WellDefined CGroup {a} {b} {c} {d} x y = additionWellDefined {a} {c} {b} {d} x y
Group.0G CGroup = injection 0G
Group.inverse CGroup = -C_
Group.+Associative CGroup {a} {b} {c} = Cassoc {a} {b} {c}
Group.identRight CGroup {a} = CidentRight {a}
Group.identLeft CGroup {a} = CidentLeft {a}
Group.invLeft CGroup {a} = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {(-C a) +C a} {a +C (-C a)} {injection 0G} (+CCommutative { -C a} {a}) (CinvRight {a})
Group.invRight CGroup {a} = CinvRight {a}

CInjectionGroupHom : GroupHom (Ring.additiveGroup R) CGroup injection
GroupHom.groupHom CInjectionGroupHom {x} {y} = additionHom x y
GroupHom.wellDefined CInjectionGroupHom {x} {y} x=y = SetoidInjection.wellDefined CInjection {x} {y} x=y
