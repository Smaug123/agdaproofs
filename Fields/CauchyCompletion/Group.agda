{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Groups.Homomorphisms.Definition
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions.Definition
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Fields.CauchyCompletion.Group {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open TotallyOrderedRing order
open Field F
open Group (Ring.additiveGroup R)
open Ring R

open import Rings.Orders.Total.Lemmas order
open import Rings.Orders.Total.AbsoluteValue order
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Addition order F
open import Fields.CauchyCompletion.Setoid order F

abstract
  +CCommutative : (a b : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid (a +C b) (b +C a)
  +CCommutative a b ε 0<e = 0 , ans
    where
      foo : {x y : A} → (x + y) + inverse (y + x) ∼ 0G
      foo = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (inverseWellDefined additiveGroup groupIsAbelian)) invRight
      ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (a +C b)) (map inverse (CauchyCompletion.elts (b +C a)))) m) < ε
      ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a +C b)) (map inverse (CauchyCompletion.elts (b +C a))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _+_ {m} | equalityCommutative (mapAndIndex (apply _+_ (CauchyCompletion.elts b) (CauchyCompletion.elts a)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts a) _+_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ foo) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

private
  abstract
    additionWellDefinedLeft : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a +C c) (b +C c)
    additionWellDefinedLeft record { elts = a ; converges = aConv } record { elts = b ; converges = bConv } record { elts = c ; converges = cConv } a=b ε 0<e with a=b ε 0<e
    ... | Na-b , prA-b = Na-b , ans
      where
        ans : {m : ℕ} → Na-b <N m → abs (index (apply _+_ (apply _+_ a c) (map inverse (apply _+_ b c))) m) < ε
        ans {m} mBig with prA-b {m} mBig
        ... | bl rewrite indexAndApply (apply _+_ a c) (map inverse (apply _+_ b c)) _+_ {m} | indexAndApply a c _+_ {m} | equalityCommutative (mapAndIndex (apply _+_ b c) inverse m) | indexAndApply b c _+_ {m} = <WellDefined (absWellDefined _ _ t) (Equivalence.reflexive eq) bl
          where
            t : index (apply _+_ a (map inverse b)) m ∼ ((index a m + index c m) + inverse (index b m + index c m))
            t rewrite indexAndApply a (map inverse b) _+_ {m} | equalityCommutative (mapAndIndex b inverse m) = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq identLeft) (+WellDefined (Equivalence.symmetric eq invRight) (Equivalence.reflexive eq))) (Equivalence.symmetric eq +Associative)) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (invContravariant additiveGroup))))) (+Associative {index a m})

    additionPreservedLeft : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (injection a +C c) (injection b +C c)
    additionPreservedLeft {a} {b} {c} a=b = additionWellDefinedLeft (injection a) (injection b) c (injectionPreservesSetoid a b a=b)

    additionPreservedRight : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (c +C injection a) (c +C injection b)
    additionPreservedRight {a} {b} {c} a=b = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {c +C injection a} {injection a +C c} {c +C injection b} (+CCommutative c (injection a)) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a +C c} {injection b +C c} {c +C injection b} (additionPreservedLeft {a} {b} {c} a=b) (+CCommutative (injection b) c))

    additionPreserved : {a b c d : A} → (a ∼ b) → (c ∼ d) → Setoid._∼_ cauchyCompletionSetoid (injection a +C injection c) (injection b +C injection d)
    additionPreserved {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a +C injection c} {injection a +C injection d} {injection b +C injection d} (additionPreservedRight {c} {d} {injection a} c=d) (additionPreservedLeft {a} {b} {injection d} a=b)

    additionWellDefinedRight : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid b c → Setoid._∼_ cauchyCompletionSetoid (a +C b) (a +C c)
    additionWellDefinedRight a b c b=c = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a +C b} {b +C a} {a +C c} (+CCommutative a b) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {b +C a} {c +C a} {a +C c} (additionWellDefinedLeft b c a b=c) (+CCommutative c a))

    additionWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → Setoid._∼_ cauchyCompletionSetoid (a +C c) (b +C d)
    additionWellDefined {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a +C c} {a +C d} {b +C d} (additionWellDefinedRight a c d c=d) (additionWellDefinedLeft a b d a=b)

    additionHom : (x y : A) → Setoid._∼_ cauchyCompletionSetoid (injection (x + y)) (injection x +C injection y)
    additionHom x y ε 0<e = 0 , ans
      where
        ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (injection (x + y))) (map inverse (CauchyCompletion.elts (injection x +C injection y)))) m) < ε
        ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (injection (x + y))) (map inverse (CauchyCompletion.elts (injection x +C injection y))) _+_ {m} | equalityCommutative (mapAndIndex (apply _+_ (constSequence x) (constSequence y)) inverse m) | indexAndConst (x + y) m | indexAndApply (constSequence x) (constSequence y) _+_ {m} | indexAndConst x m | indexAndConst y m = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ invRight) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

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
    CidentLeft {a} = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection 0G +C a} {a +C injection 0G} {a} (+CCommutative (injection 0G) a) (CidentRight {a})

    CinvRight : {a : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a +C (-C a)) (injection 0G)
    CinvRight {a} ε 0<e = 0 , ans
      where
        ans : {m : ℕ} → (0 <N m) → abs (index (apply _+_ (CauchyCompletion.elts (a +C (-C a))) (map inverse (CauchyCompletion.elts (injection 0G)))) m) < ε
        ans {m} 0<m rewrite indexAndApply (CauchyCompletion.elts (a +C (-C a))) (map inverse (CauchyCompletion.elts (injection 0G))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts a)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) | equalityCommutative (mapAndIndex (constSequence 0G) inverse m) | indexAndConst 0G m = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.transitive eq (+WellDefined invRight (invIdent (Ring.additiveGroup R))) identRight)) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

CGroup : Group cauchyCompletionSetoid _+C_
Group.+WellDefined CGroup {a} {b} {c} {d} x y = additionWellDefined {a} {c} {b} {d} x y
Group.0G CGroup = injection 0G
Group.inverse CGroup = -C_
Group.+Associative CGroup {a} {b} {c} = Cassoc {a} {b} {c}
Group.identRight CGroup {a} = CidentRight {a}
Group.identLeft CGroup {a} = CidentLeft {a}
Group.invLeft CGroup {a} = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {(-C a) +C a} {a +C (-C a)} {injection 0G} (+CCommutative (-C a) a) (CinvRight {a})
Group.invRight CGroup {a} = CinvRight {a}

CInjectionGroupHom : GroupHom (Ring.additiveGroup R) CGroup injection
GroupHom.groupHom CInjectionGroupHom {x} {y} = additionHom x y
GroupHom.wellDefined CInjectionGroupHom {x} {y} x=y = SetoidInjection.wellDefined CInjection {x} {y} x=y
