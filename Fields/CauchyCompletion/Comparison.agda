{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Groups
open import Groups.Lemmas
open import Fields.Fields
open import Fields.Orders.Total.Definition
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Semirings.Definition

module Fields.CauchyCompletion.Comparison {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

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
open import Fields.CauchyCompletion.Setoid order F charNot2

-- "<C rational", where the r indicates where the rational number goes
_<Cr_ : CauchyCompletion → A → Set (m ⊔ o)
a <Cr b = Sg A (λ ε → (0G < ε) && Sg ℕ (λ N → ((m : ℕ) → (N<m : N <N m) → (ε + index (CauchyCompletion.elts a) m) < b)))

<CrWellDefinedRight : (a : CauchyCompletion) (b c : A) → b ∼ c → a <Cr b → a <Cr c
<CrWellDefinedRight a b c b=c (ε , (0<e ,, (N , pr))) = ε , (0<e ,, (N , λ m N<m → <WellDefined (Equivalence.reflexive eq) b=c (pr m N<m)))

<CrWellDefinedLemma : (a b e/2 e : A) (0<e : 0G < e) (pr : e/2 + e/2 ∼ e) → abs (a + inverse b) < e/2 → (e/2 + b) < (e + a)
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e with totality 0G (a + inverse b)
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e | inl (inl 0<a-b) = ringAddInequalities (halfLess e/2 e 0<e pr) (<WellDefined identLeft (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) invLeft) identRight)) (orderRespectsAddition 0<a-b b))
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e | inl (inr a-b<0) = <WellDefined (Equivalence.transitive eq (+WellDefined (invContravariant (Ring.additiveGroup R)) groupIsAbelian) (Equivalence.transitive eq (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (invTwice additiveGroup b) invLeft) identRight)) (Equivalence.reflexive eq))) groupIsAbelian)) (Equivalence.transitive eq +Associative (+WellDefined pr (Equivalence.reflexive eq))) (orderRespectsAddition a-b<e (e/2 + a))
<CrWellDefinedLemma a b e/2 e 0<e pr a-b<e | inr 0=a-b = <WellDefined (Equivalence.reflexive eq) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (transferToRight (Ring.additiveGroup R) (Equivalence.symmetric eq 0=a-b)))) (orderRespectsAddition (halfLess e/2 e 0<e pr) b)

<CrWellDefinedLeft : (a b : CauchyCompletion) (c : A) → Setoid._∼_ cauchyCompletionSetoid a b → a <Cr c → b <Cr c
<CrWellDefinedLeft a b c a=b (ε , (0<e ,, (N , pr))) with halve charNot2 ε
... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
... | 0<e/2 with a=b e/2 0<e/2
... | N2 , prN2 = e/2 , (0<e/2 ,, ((N +N N2) , ans))
  where
    ans : (m : ℕ) → (N<m : (N +N N2) <N m) → (e/2 + index (CauchyCompletion.elts b) m) < c
    ans m N<m with prN2 {m} (inequalityShrinkRight N<m)
    ... | bl rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts b) inverse m) = SetoidPartialOrder.<Transitive pOrder (<CrWellDefinedLemma (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) e/2 ε 0<e prE/2 bl) (pr m (inequalityShrinkLeft N<m))

<CrWellDefined : (a b : CauchyCompletion) (c d : A) → Setoid._∼_ cauchyCompletionSetoid a b → c ∼ d → a <Cr c → b <Cr d
<CrWellDefined a b c d a=b c=d a<c = <CrWellDefinedLeft a b d a=b (<CrWellDefinedRight a c d c=d a<c)

_r<C_ : A → CauchyCompletion → Set (m ⊔ o)
a r<C b = Sg A (λ ε → (0G < ε) && Sg ℕ (λ N → ((m : ℕ) → (N<m : N <N m) → (a + ε) < index (CauchyCompletion.elts b) m)))

r<CWellDefinedLeft : (a b : A) (c : CauchyCompletion) → (a ∼ b) → (a r<C c) → b r<C c
r<CWellDefinedLeft a b c a=b (e , (0<e ,, (N , pr))) = e , (0<e ,, (N , λ m N<m → <WellDefined (+WellDefined a=b (Equivalence.reflexive eq)) (Equivalence.reflexive eq) (pr m N<m)))

r<CWellDefinedLemma : (a b c e e/2 : A) (_ : e/2 + e/2 ∼ e) (0<e : 0G < e) (_ : abs (a + inverse b) < e/2) (_ : (c + e) < a) → (c + e/2) < b
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a with totality 0G (a + inverse b)
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inl (inl 0<a-b) = SetoidPartialOrder.<Transitive pOrder (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq prE/2) (Equivalence.reflexive eq)) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invRight)) identRight)))) (Equivalence.reflexive eq) (orderRespectsAddition c+e<a (inverse e/2))) (<WellDefined (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) invLeft) identRight)) (Equivalence.reflexive eq))) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (invLeft)) identRight))) (orderRespectsAddition pr (b + inverse e/2)))
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inl (inr a-b<0) = SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (halfLess e/2 e 0<e prE/2) c)) c+e<a) (<WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invLeft)) identRight) identLeft (orderRespectsAddition a-b<0 b))
r<CWellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inr 0=a-b = SetoidPartialOrder.<Transitive pOrder (<WellDefined groupIsAbelian (Equivalence.reflexive eq) (orderRespectsAddition (halfLess e/2 e 0<e prE/2) c)) (<WellDefined (groupIsAbelian {c} {e}) (transferToRight additiveGroup (Equivalence.symmetric eq 0=a-b)) c+e<a)

r<CWellDefinedRight : (a b : CauchyCompletion) (c : A) → Setoid._∼_ cauchyCompletionSetoid a b → c r<C a → c r<C b
r<CWellDefinedRight a b c a=b (e , (0<e ,, (N , pr))) with halve charNot2 e
... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
... | 0<e/2 with a=b e/2 0<e/2
... | N2 , prN2 = e/2 , (0<e/2 ,, ((N +N N2) , ans))
  where
    ans : (m : ℕ) → (N<m : (N +N N2) <N m) → (c + e/2) < index (CauchyCompletion.elts b) m
    ans m N<m with prN2 {m} (inequalityShrinkRight N<m)
    ... | bl rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts b) inverse m) = r<CWellDefinedLemma (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) c e e/2 prE/2 0<e bl (pr m (inequalityShrinkLeft N<m))

_<C_ : CauchyCompletion → CauchyCompletion → Set (m ⊔ o)
a <C b = Sg A (λ i → (a <Cr i) && (i r<C b))

<CWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → a <C c → b <C d
<CWellDefined {a} {b} {c} {d} a=b c=d (bound , (a<bound ,, bound<b)) = bound , (<CrWellDefinedLeft a b bound a=b a<bound ,, r<CWellDefinedRight c d bound c=d bound<b)

<CrPreserves : {a b : A} → a < b → injection a <Cr b
<CrPreserves {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = (between + inverse a) , (<WellDefined invRight (Equivalence.reflexive eq) (orderRespectsAddition a<between (inverse a)) ,, (0 , λ m _ → <WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (ans a m)) +Associative)) (Equivalence.reflexive eq) between<b))
  where
    ans : (x : A) (m : ℕ) → 0G ∼ inverse x + index (constSequence x) m
    ans x m rewrite indexAndConst x m = Equivalence.symmetric eq invLeft

r<CPreserves : {a b : A} → a < b → a r<C injection b
r<CPreserves {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = (between + inverse a) , (<WellDefined invRight (Equivalence.reflexive eq) (orderRespectsAddition a<between (inverse a)) ,, (0 , λ m _ → <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq invLeft))) +Associative) groupIsAbelian) (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (indexAndConst b m)) between<b))

<CInherited : {a b : A} → a < b → (injection a) <C (injection b)
<CInherited {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = between , (<CrPreserves a<between ,, r<CPreserves between<b)

<CInherited' : {a b : A} → (injection a) <C (injection b) → a < b
<CInherited' {a} {b} (bound , ((Na , (0<Na ,, (Na2 , prA))) ,, ((Nb , (0<Nb ,, (Nb2 , prB)))))) with prA (succ Na2) (le 0 refl)
... | bl with prB (succ Nb2) (le 0 refl)
... | bl2 rewrite indexAndConst a Na2 | indexAndConst b Nb2 = SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<Na a)) bl) (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<Nb bound)) bl2)

<CIrreflexive : {a : CauchyCompletion} → a <C a → False
<CIrreflexive {a} (bound , ((bA , (0<bA ,, (Na , prA))) ,, ((bB , (0<bB ,, (Nb , prB)))))) with prA (succ Na +N Nb) (le Nb (applyEquality succ (Semiring.commutative ℕSemiring Nb Na)))
... | bl with prB (succ Na +N Nb) (le Na refl)
... | bl2 with <WellDefined (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) groupIsAbelian) (Equivalence.reflexive eq))) groupIsAbelian (ringAddInequalities bl bl2)
... | bad = irreflexive (SetoidPartialOrder.<Transitive pOrder (<WellDefined identLeft +Associative (<WellDefined (Equivalence.reflexive eq) groupIsAbelian (orderRespectsAddition (<WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities 0<bA 0<bB)) (index (CauchyCompletion.elts a) (succ Na +N Nb) + bound)))) bad)

<CTransitive : {a b c : CauchyCompletion} → a <C b → b <C c → a <C c
<CTransitive {a} {b} {c} (boundA , ((eL , (0<eL ,, prL)) ,, (eR , (0<eR ,, (Nr , prR))))) (boundB , ((fL , (0<fL ,, (Nfl , prFl))) ,, (fR , (0<fR ,, (N , prFR))))) = boundA , ((eL , (0<eL ,, prL)) ,, (eR , (0<eR ,, (((Nr +N Nfl) +N N) , λ m N<m → SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (SetoidPartialOrder.<Transitive pOrder (prR m (inequalityShrinkLeft {Nr} (inequalityShrinkLeft N<m))) (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<fL (index (CauchyCompletion.elts b) m)))) (prFl m (inequalityShrinkRight {Nr} (inequalityShrinkLeft N<m)))) (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<fR boundB))) (prFR m (inequalityShrinkRight N<m))))))

<COrder : SetoidPartialOrder cauchyCompletionSetoid _<C_
SetoidPartialOrder.<WellDefined <COrder {a} {b} {c} {d} a=b c=d a<c = <CWellDefined {a} {b} {c} {d} a=b c=d a<c
SetoidPartialOrder.irreflexive <COrder {a} a<a = <CIrreflexive {a} a<a
SetoidPartialOrder.<Transitive <COrder {a} {b} {c} a<b b<c = <CTransitive {a} {b} {c} a<b b<c
