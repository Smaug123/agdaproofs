{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Semirings.Definition

module Fields.CauchyCompletion.Comparison {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Ring R
open Group additiveGroup
open Field F
open import Fields.Orders.Lemmas {F = F} {pRing} (record { oRing = order })

open import Rings.Orders.Partial.Lemmas pRing
open import Rings.Orders.Total.Lemmas order
open import Fields.Lemmas F
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Setoid order F
open import Fields.Orders.Total.Lemmas {F = F} (record { oRing = order })

-- "<C rational", where the r indicates where the rational number goes
record _<Cr_ (a : CauchyCompletion) (b : A) : Set (m ⊔ o) where
  field
    e : A
    0<e : 0G < e
    N : ℕ
    property : ((m : ℕ) → (N<m : N <N m) → (e + index (CauchyCompletion.elts a) m) < b)

<CrWellDefinedRight : (a : CauchyCompletion) (b c : A) → b ∼ c → a <Cr b → a <Cr c
<CrWellDefinedRight a b c b=c record { e = ε ; 0<e = 0<e ; N = N ; property = pr } = record { e = ε ; 0<e = 0<e ; N = N ; property = λ m N<m → <WellDefined (Equivalence.reflexive eq) b=c (pr m N<m) }

<CrWellDefinedLemma : (a b e/2 e : A) (0<e : 0G < e) (pr : e/2 + e/2 ∼ e) → abs (a + inverse b) < e/2 → (e/2 + b) < (e + a)
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e with totality 0G (a + inverse b)
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e | inl (inl 0<a-b) = ringAddInequalities (halfLess e/2 e 0<e pr) (<WellDefined identLeft (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) invLeft) identRight)) (orderRespectsAddition 0<a-b b))
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e | inl (inr a-b<0) = <WellDefined (Equivalence.transitive eq (+WellDefined (invContravariant (Ring.additiveGroup R)) groupIsAbelian) (Equivalence.transitive eq (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (invTwice additiveGroup b) invLeft) identRight)) (Equivalence.reflexive eq))) groupIsAbelian)) (Equivalence.transitive eq +Associative (+WellDefined pr (Equivalence.reflexive eq))) (orderRespectsAddition a-b<e (e/2 + a))
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e | inr 0=a-b = <WellDefined (Equivalence.reflexive eq) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (transferToRight (Ring.additiveGroup R) (Equivalence.symmetric eq 0=a-b)))) (orderRespectsAddition (halfLess e/2 e 0<e pr) b)

<CrWellDefinedLeft : (a b : CauchyCompletion) (c : A) → Setoid._∼_ cauchyCompletionSetoid a b → a <Cr c → b <Cr c
<CrWellDefinedLeft a b c a=b record { e = ε ; 0<e = 0<e ; N = N ; property = pr } with halve charNot2 ε
... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
... | 0<e/2 with a=b e/2 0<e/2
... | N2 , prN2 = record { e = e/2 ; 0<e = 0<e/2 ; N = N +N N2 ; property = ans }
  where
    ans : (m : ℕ) → (N<m : (N +N N2) <N m) → (e/2 + index (CauchyCompletion.elts b) m) < c
    ans m N<m with prN2 {m} (inequalityShrinkRight N<m)
    ... | bl rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts b) inverse m) = SetoidPartialOrder.<Transitive pOrder (<CrWellDefinedLemma (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) e/2 ε 0<e prE/2 bl) (pr m (inequalityShrinkLeft N<m))

<CrWellDefined : (a b : CauchyCompletion) (c d : A) → Setoid._∼_ cauchyCompletionSetoid a b → c ∼ d → a <Cr c → b <Cr d
<CrWellDefined a b c d a=b c=d a<c = <CrWellDefinedLeft a b d a=b (<CrWellDefinedRight a c d c=d a<c)

record _r<C_ (a : A) (b : CauchyCompletion) : Set (m ⊔ o) where
  field
    e : A
    0<e : 0G < e
    N : ℕ
    pr : (m : ℕ) → (N<m : N <N m) → (a + e) < index (CauchyCompletion.elts b) m

r<CWellDefinedLeft : (a b : A) (c : CauchyCompletion) → (a ∼ b) → (a r<C c) → b r<C c
r<CWellDefinedLeft a b c a=b record { e = e ; 0<e = 0<e ; N = N ; pr = pr } = record { e = e ; 0<e = 0<e ; N = N ; pr =  λ m N<m → <WellDefined (+WellDefined a=b (Equivalence.reflexive eq)) (Equivalence.reflexive eq) (pr m N<m) }

r<CWellDefinedLemma : (a b c e e/2 : A) (_ : e/2 + e/2 ∼ e) (0<e : 0G < e) (_ : abs (a + inverse b) < e/2) (_ : (c + e) < a) → (c + e/2) < b
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a with totality 0G (a + inverse b)
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inl (inl 0<a-b) = SetoidPartialOrder.<Transitive pOrder (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq prE/2) (Equivalence.reflexive eq)) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invRight)) identRight)))) (Equivalence.reflexive eq) (orderRespectsAddition c+e<a (inverse e/2))) (<WellDefined (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) invLeft) identRight)) (Equivalence.reflexive eq))) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (invLeft)) identRight))) (orderRespectsAddition pr (b + inverse e/2)))
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inl (inr a-b<0) = SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (halfLess e/2 e 0<e prE/2) c)) c+e<a) (<WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invLeft)) identRight) identLeft (orderRespectsAddition a-b<0 b))
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inr 0=a-b = SetoidPartialOrder.<Transitive pOrder (<WellDefined groupIsAbelian (Equivalence.reflexive eq) (orderRespectsAddition (halfLess e/2 e 0<e prE/2) c)) (<WellDefined (groupIsAbelian {c} {e}) (transferToRight additiveGroup (Equivalence.symmetric eq 0=a-b)) c+e<a)

r<CWellDefinedRight : (a b : CauchyCompletion) (c : A) → Setoid._∼_ cauchyCompletionSetoid a b → c r<C a → c r<C b
r<CWellDefinedRight a b c a=b record { e = e ; 0<e = 0<e ; N = N ; pr = pr } with halve charNot2 e
... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
... | 0<e/2 with a=b e/2 0<e/2
... | N2 , prN2 = record { e = e/2 ; 0<e = 0<e/2 ; N = N +N N2 ; pr = ans }
  where
    ans : (m : ℕ) → (N<m : (N +N N2) <N m) → (c + e/2) < index (CauchyCompletion.elts b) m
    ans m N<m with prN2 {m} (inequalityShrinkRight N<m)
    ... | bl rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts b) inverse m) = r<CWellDefinedLemma (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) c e e/2 prE/2 0<e bl (pr m (inequalityShrinkLeft N<m))

record _<C_ (a : CauchyCompletion) (b : CauchyCompletion) : Set (m ⊔ o) where
  field
    i : A
    a<i : a <Cr i
    i<b : i r<C b

<CWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → a <C c → b <C d
<CWellDefined {a} {b} {c} {d} a=b c=d record { i = bound ; a<i = a<bound ; i<b = bound<b } = record { i = bound ; a<i = <CrWellDefinedLeft a b bound a=b a<bound ; i<b = r<CWellDefinedRight c d bound c=d bound<b }

<CInheritedL : {a b : A} → a < b → injection a <Cr b
<CInheritedL {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = record { e = between + inverse a ; 0<e = <WellDefined invRight (Equivalence.reflexive eq) (orderRespectsAddition a<between (inverse a)) ; N = 0 ; property = λ m _ → <WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (ans a m)) +Associative)) (Equivalence.reflexive eq) between<b }
  where
    ans : (x : A) (m : ℕ) → 0G ∼ inverse x + index (constSequence x) m
    ans x m rewrite indexAndConst x m = Equivalence.symmetric eq invLeft

<CInheritedR : {a b : A} → a < b → a r<C injection b
<CInheritedR {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = record { e = between + inverse a ; 0<e = <WellDefined invRight (Equivalence.reflexive eq) (orderRespectsAddition a<between (inverse a)) ; N = 0 ; pr = λ m _ → <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq invLeft))) +Associative) groupIsAbelian) (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (indexAndConst b m)) between<b }

<CInherited : {a b : A} → a < b → (injection a) <C (injection b)
<CInherited {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = record { i = between ; a<i = <CInheritedL a<between ; i<b = <CInheritedR between<b }

<CCollapsesL : (a b : A) → (injection a) <Cr b → a < b
<CCollapsesL a b record { e = e ; 0<e = 0<i ; N = N ; property = pr } with pr (succ N) (le 0 refl)
... | bl rewrite indexAndConst a N = <Transitive (<WellDefined identLeft reflexive (orderRespectsAddition 0<i a)) bl

<CCollapsesR : (a b : A) → a r<C injection b → a < b
<CCollapsesR a b record { e = e ; 0<e = 0<e ; N = N ; pr = pr } with pr (succ N) (le 0 refl)
... | bl rewrite indexAndConst b N = <Transitive (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<e a)) bl

<CCollapses : {a b : A} → (injection a) <C (injection b) → a < b
<CCollapses {a} {b} record { i = inter ; a<i = pr1 ; i<b = pr2 } = <Transitive (<CCollapsesL a inter pr1) (<CCollapsesR inter b pr2)

<CRelaxL : {a : A} {b : CauchyCompletion} → a r<C b → injection a <C b
<CRelaxL {a} {b} record { e = e ; 0<e = 0<e ; N = N ; pr = pr } with halve charNot2 e
... | e/2 , e/2pr = record { i = a + e/2 ; a<i = <CInheritedL (<WellDefined identLeft groupIsAbelian (orderRespectsAddition (halvePositive' e/2pr 0<e) a)) ; i<b = record { e = e/2 ; 0<e = halvePositive' e/2pr 0<e ; N = N ; pr = λ m N<m → <WellDefined (transitive (+WellDefined reflexive (symmetric e/2pr)) +Associative) reflexive (pr m N<m) } }

<CRelaxL' : {a : A} {b : CauchyCompletion} → injection a <C b → a r<C b
<CRelaxL' {a} {b} record { i = i ; a<i = a<i ; i<b = record { e = e ; 0<e = 0<e ; N = N ; pr = pr } } = record { e = e ; 0<e = 0<e ; N = N ; pr = λ m N<m → <Transitive (orderRespectsAddition (<CCollapsesL _ _ a<i) e) (pr m N<m) }

<CRelaxR : {a : CauchyCompletion} {b : A} → a <Cr b → a <C injection b
<CRelaxR {a} {b} record { e = ε ; 0<e = 0<ε ; N = N ; property = property } with halve charNot2 ε
... | e/2 , e/2+e/2=e = record { i = b + inverse e/2 ; a<i = record { e = e/2 ; 0<e = halvePositive' e/2+e/2=e 0<ε ; N = N ; property = λ m N<m → <WellDefined (transitive groupIsAbelian (transitive +Associative (+WellDefined (transitive (+WellDefined reflexive (symmetric e/2+e/2=e)) (transitive +Associative (transitive (+WellDefined invLeft reflexive) identLeft))) reflexive))) reflexive (orderRespectsAddition (property m N<m) (inverse e/2)) } ; i<b = <CInheritedR (<WellDefined groupIsAbelian identLeft (orderRespectsAddition (<WellDefined reflexive (invIdent additiveGroup) (ringSwapNegatives (<WellDefined (symmetric (invTwice additiveGroup 0R)) (symmetric (invTwice additiveGroup e/2)) (halvePositive' e/2+e/2=e 0<ε)))) b)) }

<CRelaxR' : {a : CauchyCompletion} {b : A} → a <C injection b → a <Cr b
<CRelaxR' {a} {b} record { i = i ; a<i = record { e = ε ; 0<e = 0<ε ; N = N ; property = property } ; i<b = i<b } = record { e = ε ; 0<e = 0<ε ; N = N ; property = λ m N<m → <Transitive (property m N<m) (<CCollapsesR _ _ i<b) }

<CIrreflexive : {a : CauchyCompletion} → a <C a → False
<CIrreflexive {a} record { i = bound ; a<i = record { e = bA ; 0<e = 0<bA ; N = Na ; property = prA } ; i<b = record { e = bB ; 0<e = 0<bB ; N = Nb ; pr = prB } } with prA (succ Na +N Nb) (le Nb (applyEquality succ (Semiring.commutative ℕSemiring Nb Na)))
... | bl with prB (succ Na +N Nb) (le Na refl)
... | bl2 with <WellDefined (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) groupIsAbelian) (Equivalence.reflexive eq))) groupIsAbelian (ringAddInequalities bl bl2)
... | bad = irreflexive (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft +Associative (<WellDefined (Equivalence.reflexive eq) groupIsAbelian (orderRespectsAddition (<WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities 0<bA 0<bB)) (index (CauchyCompletion.elts a) (succ Na +N Nb) + bound)))) bad)

<CTransitive : {a b c : CauchyCompletion} → a <C b → b <C c → a <C c
<CTransitive {a} {b} {c} record { i = boundA ; a<i = record { e = eL ; 0<e = 0<eL ; N = NL ; property = prL } ; i<b = record { e = eR ; 0<e = 0<eR ; N = Nr ; pr = prR } } record { i = boundB ; a<i = record { e = fL ; 0<e = 0<fL ; N = Nfl ; property = prFl } ; i<b = record { e = fR ; 0<e = 0<fR ; N = N ; pr = prFR } } = record { i = boundA ; a<i = record { e = eL ; 0<e = 0<eL ; N = NL ; property = prL } ; i<b = record { e = eR ; 0<e = 0<eR ; N = (Nr +N Nfl) +N N ; pr = λ m N<m → SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (prR m (inequalityShrinkLeft {Nr} (inequalityShrinkLeft N<m))) (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<fL (index (CauchyCompletion.elts b) m)))) (prFl m (inequalityShrinkRight {Nr} (inequalityShrinkLeft N<m)))) (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<fR boundB))) (prFR m (inequalityShrinkRight N<m)) } }

<COrder : SetoidPartialOrder cauchyCompletionSetoid _<C_
SetoidPartialOrder.<WellDefined <COrder {a} {b} {c} {d} a=b c=d a<c = <CWellDefined {a} {b} {c} {d} a=b c=d a<c
SetoidPartialOrder.irreflexive <COrder {a} a<a = <CIrreflexive {a} a<a
SetoidPartialOrder.<Transitive <COrder {a} {b} {c} a<b b<c = <CTransitive {a} {b} {c} a<b b<c
