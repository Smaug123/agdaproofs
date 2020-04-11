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
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Semirings.Definition
open import Groups.Homomorphisms.Definition
open import Rings.Homomorphisms.Definition

module Fields.CauchyCompletion.PartiallyOrderedRing {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

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
open import Fields.CauchyCompletion.Ring order F
open import Fields.CauchyCompletion.Comparison order F
open import Fields.CauchyCompletion.Setoid order F

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


-- a  < a'
-- b' < b
-- then:
-- a +C c < a' + c ~ a' + c' < b' + c' ~ b' + c < b +C c
{-
Have: a <Cr x r<C b

* Let e = min(distance from a to witness of a<x, distance from x to witness of x<b)
* Approximate a above to within e/2
* Approximate b below to within e/2
* Approximate c (above or below) to within e/2

Then a' + c' is an appropriate witness.
-}

cOrderRespectsAdditionLeft' : (a : CauchyCompletion) (b : A) (c : A) → (a <Cr b) → (a +C injection c) <C (injection b +C injection c)
cOrderRespectsAdditionLeft' a b c record { e = e ; 0<e = 0<e ; N = N ; property = pr } = <CWellDefined {a +C injection c} {a +C injection c} {injection (b + c)} {(injection b) +C (injection c)} (Equivalence.reflexive (Setoid.eq cauchyCompletionSetoid) {a +C injection c}) (GroupHom.groupHom (RingHom.groupHom CInjectionRingHom)) (<CRelaxR (record { e = e ; 0<e = 0<e ; N = N ; property = λ m N<m → <WellDefined (transitive (symmetric +Associative) (+WellDefined reflexive (ans m))) reflexive (orderRespectsAddition (pr m N<m) c) }))
  where
    ans : (m : ℕ) → (index (CauchyCompletion.elts a) m + c) ∼ index (apply _+_ (CauchyCompletion.elts a) (constSequence c)) m
    ans m rewrite indexAndApply (CauchyCompletion.elts a) (constSequence c) _+_ {m} | indexAndConst c m = reflexive

cOrderRespectsAdditionLeft : (a : CauchyCompletion) (b : A) (c : CauchyCompletion) → (a <Cr b) → (a +C c) <C (injection b +C c)
cOrderRespectsAdditionLeft a b c a<b = {!!}

cOrderRespectsAdditionRight : (a : A) (b : CauchyCompletion) (c : CauchyCompletion) → (a r<C b) → (injection a +C c) <C (b +C c)
cOrderRespectsAdditionRight a b a<b = {!!}

cOrderRespectsAddition : (a b : CauchyCompletion) → (a <C b) → (c : CauchyCompletion) → (a +C c) <C (b +C c)
cOrderRespectsAddition a b a<b c = {!!}

{-
cOrderRespectsAddition : (a b : CauchyCompletion) → (a <C b) → (c : CauchyCompletion) → (a +C c) <C (b +C c)
cOrderRespectsAddition a b (r , ((r1 , (0<r1 ,, (N1 , prN1))) ,, (r2 , (0<r2 ,, (N2 , prN2))))) c = (a' + c') , (ans1 ,, ans2)
  where
    0<min : 0G < min r1 r2
    0<min with totality r1 r2
    0<min | inl (inl r1<r2) = 0<r1
    0<min | inl (inr r2<r1) = 0<r2
    0<min | inr r1=r2 = 0<r1
    e/2All : Sg A (λ i → i + i ∼ min r1 r2)
    e/2All = halve charNot2 (min r1 r2)
    e/2 : A
    e/2 = underlying e/2All
    prE/2 : e/2 + e/2 ∼ min r1 r2
    prE/2 with e/2All
    ... | _ , pr = pr
    0<e/2 : 0G < e/2
    0<e/2 = halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<min)
    a'All : Sg A (λ i → (a <Cr i) && (injection i +C (-C a)) <C (injection e/2))
    a' : A
    a<a' : a <Cr a'
    a'Pr : (injection a' +C (-C a)) <C (injection e/2)
    b'All : Sg A (λ i → (i r<C b) && (b +C (-C injection i)) <C (injection e/2))
    b' : A
    b'<b : b' r<C b
    b'Pr : (b +C (-C injection b')) <C (injection e/2)

    c'All : Sg A (λ i → (c <Cr i) && (injection i +C (-C c)) <C (injection e/2))
    c' : A
    c<c' : c <Cr c'
    c'Pr : (injection c' +C (-C c)) <C (injection e/2)

    -- Now a' + c' is our intervening rational
    -- and r1 suffices for the witness to a + c < a' + c'
    -- and r2 suffices for the witness to b' + c' < b + c
    -- TODO here

    ans1 : (a +C c) <Cr (a' + c')
    ans1 = r1 , (0<r1 ,, ((N1 +N N2) , ans))
      where
        ans : (m : ℕ) → (N1 +N N2) <N m → (r1 + index (CauchyCompletion.elts (a +C c)) m) < (a' + c')
        ans m N1+N2<m rewrite indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts c) _+_ {m} = <WellDefined (Equivalence.symmetric eq +Associative) reflexive (SetoidPartialOrder.<Transitive pOrder (orderRespectsAddition (prN1 m (inequalityShrinkLeft N1+N2<m)) (index (CauchyCompletion.elts c) m)) {!!})

    ans2 : (a' + c') r<C (b +C c)
    ans2 = r2 , (0<r2 ,, {!!})

    a'All = approximateAbove a e/2 0<e/2
    a' = underlying a'All
    a<a' with a'All
    ... | (_ , (x ,, _)) = x
    a'Pr with a'All
    ... | (_ , (_ ,, x)) = x
    b'All = approximateBelow b e/2 0<e/2
    b' = underlying b'All
    b'<b with b'All
    ... | (_ , (x ,, _)) = x
    b'Pr with b'All
    ... | (_ , (_ ,, x)) = x
    c'All = approximateAbove c e/2 0<e/2
    c' = underlying c'All
    c<c' with c'All
    ... | (_ , (x ,, _)) = x
    c'Pr with c'All
    ... | (_ , (_ ,, x)) = x

-}

CpOrderedRing : PartiallyOrderedRing CRing <COrder
PartiallyOrderedRing.orderRespectsAddition CpOrderedRing {a} {b} = cOrderRespectsAddition a b
PartiallyOrderedRing.orderRespectsMultiplication CpOrderedRing {a} {b} record { i = interA ; a<i = 0<interA ; i<b = interA<a } record { i = interB ; a<i = 0<interB ; i<b = interB<b } = record { i = interA * interB ; a<i = productPositives interA interB 0<interA 0<interB ; i<b = productPositives' a b interA interB (<CCollapsesL 0R _ 0<interA) (<CCollapsesL 0R _ 0<interB) interA<a interB<b }

