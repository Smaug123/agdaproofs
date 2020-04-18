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
open import Fields.Orders.Total.Definition
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Addition
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Semirings.Definition
open import Groups.Homomorphisms.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Lemmas
open import Orders.Total.Definition

module Fields.CauchyCompletion.PartiallyOrderedRing {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

private
  lemma3 : {c d : _} {C : Set c} {S : Setoid {c} {d} C} {_+_ : C → C → C} (G : Group S _+_) → ({x y : C} → Setoid._∼_ S (x + y) (y + x)) → (x y z : C) → Setoid._∼_ S (((Group.inverse G x) + y) + (x + z)) (y + z)
  lemma3 {S = S} {_+_ = _+_} G ab x y z = transitive +Associative (+WellDefined (transitive (ab {inverse x + y}) (transitive +Associative (transitive (+WellDefined invRight reflexive) identLeft))) reflexive)
    where
      open Setoid S
      open Equivalence (Setoid.eq S)
      open Group G

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Ring R
open Group additiveGroup
open Field F

open import Fields.Lemmas F
open import Rings.Orders.Partial.Lemmas pRing
open import Rings.Orders.Total.Lemmas order
open import Fields.Orders.Lemmas {F = F} {pRing} (record { oRing = order })
open import Fields.Orders.Total.Lemmas {F = F} (record { oRing = order })
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Addition order F
open import Fields.CauchyCompletion.Multiplication order F
open import Fields.CauchyCompletion.Approximation order F
open import Fields.CauchyCompletion.Group order F
open import Fields.CauchyCompletion.Ring order F
open import Fields.CauchyCompletion.Comparison order F
open import Fields.CauchyCompletion.Setoid order F
open import Groups.Homomorphisms.Lemmas CInjectionGroupHom
open import Setoids.Orders.Total.Lemmas (TotallyOrderedRing.total order)

private
  productPositives : (a b : A) → (injection 0R) <Cr a → (injection 0R) <Cr b → (injection 0R) <Cr (a * b)
  productPositives a b record { e = eA ; 0<e = 0<eA ; N = Na ; property = prA } record { e = eB ; 0<e = 0<eB ; N = Nb ; property = prB } = record { e = eA * eB ; 0<e = orderRespectsMultiplication 0<eA 0<eB ; N = Na +N Nb ; property = ans }
    where
      ans : (m : ℕ) → Na +N Nb <N m → ((eA * eB) + index (CauchyCompletion.elts (injection 0R)) m) < (a * b)
      ans m <m = <WellDefined (symmetric (transitive (+WellDefined reflexive (identityOfIndiscernablesRight _∼_ reflexive (indexAndConst 0R m))) identRight)) reflexive (ringMultiplyPositives 0<eA 0<eB (<WellDefined (transitive (+WellDefined reflexive (identityOfIndiscernablesRight _∼_ reflexive (indexAndConst 0R m))) identRight) reflexive (prA m (inequalityShrinkLeft <m))) (<WellDefined (transitive (+WellDefined reflexive (identityOfIndiscernablesRight _∼_ reflexive (indexAndConst 0R m))) identRight) reflexive (prB m (inequalityShrinkRight <m))))

  productPositives' : (a b : CauchyCompletion) (interA interB : A) → (0R < interA) → (0R < interB) → (interA r<C a) → (interB r<C b) → (interA * interB) r<C (a *C b)
  productPositives' a b interA interB 0<iA 0<iB record { e = interA' ; 0<e = 0<interA' ; N = Na ; pr = prA } record { e = interB' ; 0<e = 0<interB' ; N = Nb ; pr = prB } = record { e = interA' * interB' ; 0<e = orderRespectsMultiplication 0<interA' 0<interB' ; N = Na +N Nb ; pr = ans }
    where
      ans : (m : ℕ) → (Na +N Nb <N m) → ((interA * interB) + (interA' * interB')) < index (CauchyCompletion.elts (a *C b)) m
      ans m <m rewrite indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _*_ {m} = <Transitive (<WellDefined identRight (symmetric *DistributesOver+) (<WellDefined reflexive (+WellDefined *Commutative *Commutative) (<WellDefined reflexive (+WellDefined (symmetric *DistributesOver+) (symmetric *DistributesOver+)) (<WellDefined groupIsAbelian (transitive (transitive groupIsAbelian (transitive (symmetric +Associative) (+WellDefined *Commutative (transitive groupIsAbelian (transitive (+WellDefined reflexive *Commutative) (symmetric +Associative)))))) +Associative) (orderRespectsAddition (<WellDefined identRight reflexive (ringAddInequalities (orderRespectsMultiplication 0<iB 0<interA') (orderRespectsMultiplication 0<interB' 0<iA))) ((interA * interB) + (interA' * interB'))))))) (ringMultiplyPositives (<WellDefined identRight reflexive (ringAddInequalities 0<iA 0<interA')) (<WellDefined identRight reflexive (ringAddInequalities 0<iB 0<interB')) (prA m (inequalityShrinkLeft <m)) (prB m (inequalityShrinkRight <m)))

  <COrderRespectsMultiplication : (a b : CauchyCompletion) → (injection 0R <C a) → (injection 0R <C b) → (injection 0R <C (a *C b))
  <COrderRespectsMultiplication a b record { i = interA ; a<i = 0<interA ; i<b = interA<a } record { i = interB ; a<i = 0<interB ; i<b = interB<b } = record { i = interA * interB ; a<i = productPositives interA interB 0<interA 0<interB ; i<b = productPositives' a b interA interB (<CCollapsesL 0R _ 0<interA) (<CCollapsesL 0R _ 0<interB) interA<a interB<b }

  cOrderRespectsAdditionLeft' : (a : CauchyCompletion) (b : A) (c : A) → (a <Cr b) → (a +C injection c) <C (injection b +C injection c)
  cOrderRespectsAdditionLeft' a b c record { e = e ; 0<e = 0<e ; N = N ; property = pr } = <CWellDefined {a +C injection c} {a +C injection c} {injection (b + c)} {(injection b) +C (injection c)} (Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {a +C injection c}) (GroupHom.groupHom (RingHom.groupHom CInjectionRingHom)) (<CRelaxR (record { e = e ; 0<e = 0<e ; N = N ; property = λ m N<m → <WellDefined (transitive (symmetric +Associative) (+WellDefined reflexive (ans m))) reflexive (orderRespectsAddition (pr m N<m) c) }))
    where
      ans : (m : ℕ) → (index (CauchyCompletion.elts a) m + c) ∼ index (apply _+_ (CauchyCompletion.elts a) (constSequence c)) m
      ans m rewrite indexAndApply (CauchyCompletion.elts a) (constSequence c) _+_ {m} | indexAndConst c m = reflexive

  l1 : (a : A) (b : CauchyCompletion) → a r<C b → 0R r<C (b +C injection (inverse a))
  l1 a b record { e = e ; 0<e = 0<e ; N = N ; pr = pr } = record { e = e ; 0<e = 0<e ; N = N ; pr = λ m N<m → <WellDefined (transitive groupIsAbelian (transitive +Associative (+WellDefined invLeft reflexive))) (ans m) (orderRespectsAddition (pr m N<m) (inverse a)) }
    where
      ans : (m : ℕ) → (index (CauchyCompletion.elts b) m + inverse a) ∼ index (CauchyCompletion.elts (b +C injection (inverse a))) m
      ans m rewrite indexAndApply (CauchyCompletion.elts b) (constSequence (inverse a)) _+_ {m} | indexAndConst (inverse a) m = reflexive

  l1' : (a : A) (b : CauchyCompletion) → 0R r<C (b +C injection a) → (inverse a) r<C b
  l1' a b record { e = e ; 0<e = 0<e ; N = N ; pr = pr } = record { e = e ; 0<e = 0<e ; N = N ; pr = λ m N<m → <WellDefined (transitive (+WellDefined identLeft reflexive) groupIsAbelian) (symmetric (ans m)) (orderRespectsAddition (pr m N<m) (inverse a)) }
    where
      ans : (m : ℕ) → (index (CauchyCompletion.elts b) m) ∼ (index (CauchyCompletion.elts (b +C injection a)) m + inverse a)
      ans m rewrite indexAndApply (CauchyCompletion.elts b) (constSequence a) _+_ {m} | indexAndConst a m = transitive (symmetric identRight) (transitive (+WellDefined reflexive (symmetric invRight)) +Associative)

  l2 : (a : CauchyCompletion) (b : A) → a <Cr b → 0R r<C (injection b +C (-C a))
  l2 a b record { e = e ; 0<e = 0<e ; N = N ; property = property } = record { e = e ; 0<e = 0<e ; N = N ; pr = λ m N<m → <WellDefined (transitive (transitive (symmetric +Associative) (+WellDefined reflexive invRight)) groupIsAbelian) (ans m) (orderRespectsAddition (property m N<m) (inverse (index (CauchyCompletion.elts a) m))) }
    where
      ans : (m : ℕ) → (b + inverse (index (CauchyCompletion.elts a) m)) ∼ index (CauchyCompletion.elts (injection b +C (-C a))) m
      ans m rewrite indexAndApply (CauchyCompletion.elts (injection b)) (CauchyCompletion.elts (-C a)) _+_ {m} | indexAndConst b m | mapAndIndex (CauchyCompletion.elts a) inverse m = reflexive

  l2' : (a : CauchyCompletion) (b : A) → 0R r<C (injection b +C a) → (-C a) <Cr b
  l2' a b record { e = e ; 0<e = 0<e ; N = N ; pr = pr } = record { e = e ; 0<e = 0<e ; N = N ; property = λ m N<m → <WellDefined (+WellDefined identLeft reflexive) (ans m) (orderRespectsAddition (pr m N<m) (index (CauchyCompletion.elts (-C a)) m)) }
    where
      ans : (m : ℕ) → (index (CauchyCompletion.elts (injection b +C a)) m + index (map inverse (CauchyCompletion.elts a)) m) ∼ b
      ans m rewrite indexAndApply (CauchyCompletion.elts (injection b)) (CauchyCompletion.elts a) _+_ {m} | indexAndConst b m | equalityCommutative (mapAndIndex (CauchyCompletion.elts a) inverse m) = transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)

  invInj : (i : A) → Setoid._∼_ cauchyCompletionSetoid (injection (inverse i) +C injection i) (injection 0R)
  invInj i = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection (inverse i) +C injection i) }} {record { converges = CauchyCompletion.converges ((-C (injection i)) +C injection i) }} {record { converges = CauchyCompletion.converges (injection 0R) }} (Group.+WellDefinedLeft CGroup {record { converges = CauchyCompletion.converges (injection (inverse i)) }} {record { converges = CauchyCompletion.converges (injection i)}} {record { converges = CauchyCompletion.converges (-C (injection i)) }} homRespectsInverse) (Group.invLeft CGroup {injection i})

  cOrderMove : (a b : A) (c : CauchyCompletion) → (injection a +C c) <Cr b → a r<C (injection b +C (-C c))
  cOrderMove a b c record { e = e ; 0<e = 0<e ; N = N ; property = property } = record { e = e ; 0<e = 0<e ; N = N ; pr = λ m N<m → <WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive (transitive (+WellDefined (identityOfIndiscernablesRight _∼_ reflexive (indexAndApply (CauchyCompletion.elts (injection a)) (CauchyCompletion.elts c) _+_ {m})) reflexive) (transitive (symmetric +Associative) (transitive (+WellDefined (identityOfIndiscernablesRight _∼_ reflexive (indexAndConst a m)) invRight) identRight)))) groupIsAbelian)) (transitive (+WellDefined (identityOfIndiscernablesLeft _∼_ reflexive (indexAndConst b m)) (identityOfIndiscernablesRight _∼_ reflexive (mapAndIndex (CauchyCompletion.elts c) inverse m))) (identityOfIndiscernablesLeft _∼_ reflexive (indexAndApply (CauchyCompletion.elts (injection b)) (CauchyCompletion.elts (-C c)) _+_ {m}))) (orderRespectsAddition (property m N<m) (inverse (index (CauchyCompletion.elts c) m))) }

  cOrderMove' : (a b : A) (c : CauchyCompletion) → (injection a +C (-C c)) <Cr b → a r<C (injection b +C c)
  cOrderMove' a b c pr = r<CWellDefinedRight _ _ _ (Group.+WellDefinedRight CGroup {record { converges = CauchyCompletion.converges (injection b) }} {record { converges = CauchyCompletion.converges (-C (-C c)) }} {record {converges = CauchyCompletion.converges c }} (invTwice CGroup record { converges = CauchyCompletion.converges c })) (cOrderMove a b (-C c) pr)

  cOrderMove'' : (a : CauchyCompletion) (b c : A) → (a +C (-C injection b)) <Cr c → a <Cr (b + c)
  cOrderMove'' a b c record { e = e ; 0<e = 0<e ; N = N ; property = property } = record { e = e ; 0<e = 0<e ; N = N ; property = λ m N<m → <WellDefined (transitive (symmetric +Associative) (+WellDefined reflexive (transitive (+WellDefined (identityOfIndiscernablesRight _∼_ reflexive (indexAndApply (CauchyCompletion.elts a) _ _+_ {m})) reflexive) (transitive (transitive (symmetric +Associative) (+WellDefined reflexive (transitive (+WellDefined (transitive (identityOfIndiscernablesLeft _∼_ reflexive (mapAndIndex _ inverse m)) (inverseWellDefined additiveGroup (identityOfIndiscernablesRight _∼_ reflexive (indexAndConst b m)))) reflexive) invLeft))) identRight)))) groupIsAbelian (orderRespectsAddition (property m N<m) b) }

  cOrderRespectsAdditionLeft'' : (a b : A) (c : CauchyCompletion) → (a < b) → (injection a +C c) <C (injection b +C c)
  cOrderRespectsAdditionLeft'' a b c a<b with halve charNot2 (b + inverse a)
  ... | b-a/2 , prDiff with approximateAbove c b-a/2 (halvePositive' prDiff (moveInequality a<b))
  ... | aboveC , (c<aboveC ,, aboveC-C<e) = record { i = a + aboveC ; a<i = <CRelaxR' (SetoidPartialOrder.<WellDefined <COrder (Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges c }} {record { converges = CauchyCompletion.converges (injection a) }}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection aboveC +C injection a) }} {record { converges = CauchyCompletion.converges (injection a +C injection aboveC) }} {record { converges = CauchyCompletion.converges (injection (a + aboveC)) }} (Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges (injection aboveC) }} {record { converges = CauchyCompletion.converges (injection a) }}) (Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection (a + aboveC)) }} {record { converges = CauchyCompletion.converges (injection a +C injection aboveC) }} (GroupHom.groupHom CInjectionGroupHom))) (cOrderRespectsAdditionLeft' c aboveC a c<aboveC)) ; i<b = cOrderMove' _ _ _ (<CRelaxR' (<CTransitive (<CRelaxR t) (<CInherited u))) }
    where
      g : ((injection aboveC +C (-C c)) +C injection a) <C ((injection b-a/2) +C (injection a))
      g = cOrderRespectsAdditionLeft' _ _ a (<CRelaxR' aboveC-C<e)
      g' : ((injection aboveC +C (-C c)) +C injection a) <C (injection (b-a/2 + a))
      g' = <CWellDefined (Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges ((injection aboveC +C (-C c)) +C injection a) }}) (Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection (b-a/2 + a)) }} {record { converges = CauchyCompletion.converges (injection b-a/2 +C injection a) }} (GroupHom.groupHom CInjectionGroupHom)) g
      t : (injection (a + aboveC) +C (-C c)) <Cr (b-a/2 + a)
      t = <CRelaxR' (<CWellDefined (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (((injection aboveC) +C (-C c)) +C injection a) }} {record { converges = CauchyCompletion.converges (injection a +C ((injection aboveC) +C (-C c))) }} {record { converges = CauchyCompletion.converges (injection (a + aboveC) +C (-C c)) }} (Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges (injection aboveC +C (-C c)) }} {record { converges = CauchyCompletion.converges (injection a) }}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection a +C ((injection aboveC) +C (-C c))) }} {record { converges = CauchyCompletion.converges (((injection a) +C (injection aboveC)) +C (-C c)) }} {record { converges = CauchyCompletion.converges ((injection (a + aboveC)) +C (-C c)) }} (Group.+Associative CGroup {record { converges = CauchyCompletion.converges (injection a) }} {record { converges = CauchyCompletion.converges (injection aboveC) }} {record { converges = CauchyCompletion.converges (-C c) }}) (Group.+WellDefinedLeft CGroup {record { converges = CauchyCompletion.converges (injection a +C injection aboveC) }} {record { converges = CauchyCompletion.converges (-C c) }} {record { converges = CauchyCompletion.converges (injection (a + aboveC)) }} (Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection (a + aboveC)) }} {record { converges = CauchyCompletion.converges (injection a +C injection aboveC) }} (GroupHom.groupHom CInjectionGroupHom))))) (Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection (b-a/2 + a)) }}) g')
      lemm : 0R < b-a/2
      lemm = halvePositive' prDiff (moveInequality a<b)
      u : (b-a/2 + a) < b
      u = <WellDefined (transitive (+WellDefined (symmetric prDiff) reflexive) (transitive groupIsAbelian (transitive +Associative (transitive (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) reflexive) groupIsAbelian)))) (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) (orderRespectsAddition (<WellDefined identLeft (transitive (transitive +Associative (transitive (+WellDefined (transitive groupIsAbelian (+WellDefined reflexive (symmetric (invTwice additiveGroup b-a/2)))) reflexive) (symmetric +Associative))) (+WellDefined reflexive (symmetric (invContravariant additiveGroup)))) (orderRespectsAddition lemm (b + inverse a))) (a + inverse b-a/2))

  cOrderRespectsAdditionLeft''Flip : (a b : A) (c : CauchyCompletion) → (a < b) → (c +C injection a) <C (c +C injection b)
  cOrderRespectsAdditionLeft''Flip a b c a<b = <CWellDefined ((Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges (injection a) }} {record { converges = CauchyCompletion.converges c }})) (Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges (injection b) }} {record { converges = CauchyCompletion.converges c }}) (cOrderRespectsAdditionLeft'' a b c a<b)

  cOrderRespectsAdditionLeft''' : (a b : CauchyCompletion) (c : A) → (a <C b) → (a +C injection c) <C (b +C injection c)
  cOrderRespectsAdditionLeft''' a b c record { i = i ; a<i = a<i ; i<b = i<b } = <CTransitive (cOrderRespectsAdditionLeft' a i c a<i) (<CWellDefined (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (injection (c + i)) }} {record { converges = CauchyCompletion.converges (injection c +C injection i) }} {record { converges = CauchyCompletion.converges (injection i +C injection c) }} (GroupHom.groupHom CInjectionGroupHom) (Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges (injection c) }} {record { converges = CauchyCompletion.converges (injection i) }})) (Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges (injection c) }} {record { converges = CauchyCompletion.converges b }}) (flip<C' {record { converges = CauchyCompletion.converges (injection (c + i)) }} {record { converges = CauchyCompletion.converges (injection c +C b) }} (<CWellDefined (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges ((-C b) +C injection (inverse c)) }} {record { converges = CauchyCompletion.converges ((-C b) +C (-C (injection c))) }} {record { converges = CauchyCompletion.converges (-C (injection c +C b)) }} (Group.+WellDefinedRight CGroup {record { converges = CauchyCompletion.converges (-C b) }} {record { converges = CauchyCompletion.converges (injection (inverse c)) }} {record { converges = CauchyCompletion.converges (-C (injection c)) }} homRespectsInverse) (Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (-C (injection c +C b)) }} {record { converges = CauchyCompletion.converges ((-C b) +C (-C (injection c))) }} (invContravariant CGroup {record { converges = CauchyCompletion.converges (injection c) }} {record { converges = CauchyCompletion.converges b }}))) homRespectsInverse' (cOrderRespectsAdditionLeft' (-C b) (inverse i) (inverse c) (flipR<C i<b)))))

  cOrderRespectsAdditionRightZero : (a : CauchyCompletion) → (0R r<C a) → (c : CauchyCompletion) → c <C (a +C c)
  cOrderRespectsAdditionRightZero a record { e = e ; 0<e = 0<e ; N = N1 ; pr = pr } c with halve charNot2 e
  ... | e/2 , prE/2 with approximateAbove c e/2 (halvePositive' prE/2 0<e)
  ... | c+ , (c<c+ ,, c+<c+e/2) with approximateBelow (a +C c) e/2 (halvePositive' prE/2 0<e)
  ... | α , (α<a+c ,, a+c<α+e/2) with totality c+ α
  ... | inl (inl c+<α) = record { i = α ; a<i = <CRelaxR' (<CTransitive (<CRelaxR c<c+) (<CInherited c+<α)) ; i<b = α<a+c }
  -- The remaining cases can't actually happen, but it's easier to go this way
  ... | inr c+=α = record { i = α ; a<i = <CrWellDefinedRight c _ _ c+=α c<c+ ; i<b = α<a+c }
  ... | inl (inr α<c+) with cOrderMove'' (a +C c) α e/2 (<CRelaxR' a+c<α+e/2)
  ... | record { e = f ; 0<e = 0<f ; N = M ; property = pr2 } with CauchyCompletion.converges c e/2 (halvePositive' prE/2 0<e)
  ... | N3 , pr4 = record { i = α ; a<i = record { e = f ; 0<e = 0<f ; N = u ; property = ans } ; i<b = α<a+c }
    where
      u : ℕ
      u = succ ((N1 +N M) +N N3)
      help : (m : ℕ) → u <N m → index (CauchyCompletion.elts c) m < (e/2 + index (CauchyCompletion.elts c) u)
      help m size with pr4 {m} {u} (lessTransitive (le (N1 +N M) refl) size) (le (N1 +N M) refl)
      ... | bl with totality 0G (index (CauchyCompletion.elts c) m + inverse (index (CauchyCompletion.elts c) u))
      ... | inl (inl 0<t) = <WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) reflexive (orderRespectsAddition bl (index (CauchyCompletion.elts c) u))
      ... | inl (inr cm-cU<0) = <Transitive (<WellDefined (transitive (transitive (symmetric +Associative) (+WellDefined reflexive invLeft)) identRight) reflexive (orderRespectsAddition cm-cU<0 (index (CauchyCompletion.elts c) u))) (orderRespectsAddition (halvePositive' prE/2 0<e) (index (CauchyCompletion.elts c) u))
      ... | inr (0=t) = <WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) reflexive (orderRespectsAddition bl (index (CauchyCompletion.elts c) u))
      ans : (m : ℕ) → u <N m → (f + index (CauchyCompletion.elts c) m) < α
      ans m size = <Transitive (<WellDefined reflexive +Associative (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (<Transitive (<WellDefined reflexive (transitive (+WellDefined (symmetric (transitive (+WellDefined (transitive identLeft (symmetric prE/2)) reflexive) (transitive (transitive (symmetric +Associative) (+WellDefined reflexive invRight)) identRight))) reflexive) (symmetric +Associative)) (help m size)) (<WellDefined reflexive (transitive groupIsAbelian (transitive (symmetric +Associative) (+WellDefined reflexive groupIsAbelian))) (orderRespectsAddition (pr u (le (M +N N3) (applyEquality succ (transitivity (additionNIsCommutative _ N1) (Semiring.+Associative ℕSemiring N1 M _))))) (inverse e/2 + index (CauchyCompletion.elts c) u)))) f))) (<WellDefined (transitive groupIsAbelian (transitive +Associative (+WellDefined groupIsAbelian (identityOfIndiscernablesRight _∼_ reflexive (indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts c) _+_ {u}))))) (transitive (transitive (symmetric +Associative) (+WellDefined reflexive invRight)) identRight) (orderRespectsAddition (pr2 u (le (N1 +N N3) (applyEquality succ (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring N1 _ _)) (transitivity (applyEquality (N1 +N_) (additionNIsCommutative N3 M)) (Semiring.+Associative ℕSemiring N1 _ _)))))) (inverse e/2)))

  cOrderRespectsAdditionLeft : (a : CauchyCompletion) (b : A) (c : CauchyCompletion) → (a <Cr b) → (a +C c) <C (injection b +C c)
  cOrderRespectsAdditionLeft a b c a<b = <CWellDefined {record { converges = CauchyCompletion.converges (a +C c) }}{record { converges = CauchyCompletion.converges (a +C c) }}{record { converges = CauchyCompletion.converges (((-C a) +C injection b) +C (a +C c)) }}{record { converges = CauchyCompletion.converges (injection b +C c) }} (Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (a +C c)}}) (lemma3 CGroup (λ {x} {y} → Ring.groupIsAbelian CRing {x} {y}) a (injection b) c) (cOrderRespectsAdditionRightZero ((-C a) +C injection b) (r<CWellDefinedLeft (inverse b + b) 0R ((-C a) +C injection b) invLeft (<CRelaxL' (<CWellDefined {record { converges = CauchyCompletion.converges (injection (inverse b) +C injection b) }}{record { converges = CauchyCompletion.converges (injection (inverse b + b)) }}{record { converges = CauchyCompletion.converges ((-C a) +C injection b) }}{record { converges = CauchyCompletion.converges ((-C a) +C injection b) }} (GroupHom.groupHom' CInjectionGroupHom) (Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges ((-C a) +C injection b) }}) (cOrderRespectsAdditionLeft''' _ _ b (<CRelaxL (flip<CR a<b)))))) (a +C c))

  lemma2 : (a b : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid (Group.inverse CGroup ((-C a) +C (-C b))) (a +C b)
  lemma2 a b = tr {record { converges = CauchyCompletion.converges (-C ((-C a) +C (-C b))) }} {record { converges = CauchyCompletion.converges ((-C (-C b)) +C (-C (-C a))) }} {record { converges = CauchyCompletion.converges (a +C b) }} (invContravariant CGroup {record { converges = CauchyCompletion.converges (-C a) }} {record { converges = CauchyCompletion.converges (-C b) }}) (tr {record { converges = CauchyCompletion.converges ((-C (-C b)) +C (-C (-C a))) }} {record { converges = CauchyCompletion.converges (b +C a) }} {record { converges = CauchyCompletion.converges (a +C b) }} (Group.+WellDefined CGroup {record { converges = CauchyCompletion.converges (-C (-C b)) }} {record { converges = CauchyCompletion.converges (-C (-C a)) }} {record { converges = CauchyCompletion.converges b }} {record { converges = CauchyCompletion.converges a }} (invTwice CGroup b) (invTwice CGroup a)) (Ring.groupIsAbelian CRing {record { converges = CauchyCompletion.converges b }} {record { converges = CauchyCompletion.converges a }}))
    where
      open Setoid cauchyCompletionSetoid
      open Equivalence (Setoid.eq cauchyCompletionSetoid) renaming (transitive to tr)

  cOrderRespectsAdditionRight : (a : A) (b : CauchyCompletion) (c : CauchyCompletion) → (a r<C b) → (injection a +C c) <C (b +C c)
  cOrderRespectsAdditionRight a b c a<b = <CWellDefined (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {record { converges = CauchyCompletion.converges (Group.inverse CGroup (injection (inverse a) +C (-C c))) }} {record { converges = CauchyCompletion.converges (Group.inverse CGroup ((-C injection a) +C (-C c))) }} {record { converges = CauchyCompletion.converges (injection a +C c) }} (inverseWellDefined CGroup {record { converges = CauchyCompletion.converges (injection (inverse a) +C (-C c)) }} {record { converges = CauchyCompletion.converges ((-C (injection a)) +C (-C c)) }} (Group.+WellDefinedLeft CGroup {record { converges = CauchyCompletion.converges (injection (inverse a)) }} {record { converges = CauchyCompletion.converges (-C c) }} {record { converges = CauchyCompletion.converges (-C (injection a)) }} homRespectsInverse)) (lemma2 (injection a) c)) (lemma2 b c) (flip<C (cOrderRespectsAdditionLeft _ _ (Group.inverse CGroup c) (flipR<C a<b)))

  cOrderRespectsAddition : (a b : CauchyCompletion) → (a <C b) → (c : CauchyCompletion) → (a +C c) <C (b +C c)
  cOrderRespectsAddition a b record { i = i ; a<i = a<i ; i<b = i<b } c = SetoidPartialOrder.<Transitive <COrder (cOrderRespectsAdditionLeft a i c a<i) (cOrderRespectsAdditionRight i b c i<b)

CpOrderedRing : PartiallyOrderedRing CRing <COrder
PartiallyOrderedRing.orderRespectsAddition CpOrderedRing {a} {b} = cOrderRespectsAddition a b
PartiallyOrderedRing.orderRespectsMultiplication CpOrderedRing {a} {b} 0<a 0<b = <COrderRespectsMultiplication a b 0<a 0<b
