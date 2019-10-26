{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Order
open import Groups.Definition
open import Groups.Groups
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Semirings.Definition

module Fields.CauchyCompletion.Comparison {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder {_<_ = _<_} pOrder} {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Ring R
open Group additiveGroup
open Field F
open import Fields.Orders.Lemmas {F = F} record { oRing = order }

open import Rings.Orders.Lemmas order
open import Fields.Lemmas F
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Setoid order F charNot2

shrinkInequality : {a b c : ℕ} → a +N b <N c → a <N c
shrinkInequality {a} {b} {c} (le x pr) = le (x +N b) (transitivity (applyEquality succ (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring x _ _)) (applyEquality (x +N_) (Semiring.commutative ℕSemiring b a)))) pr)

shrinkInequality' : {a b c : ℕ} → a +N b <N c → b <N c
shrinkInequality' {a} {b} {c} (le x pr) = le (x +N a) (transitivity (applyEquality succ (equalityCommutative (Semiring.+Associative ℕSemiring x _ _))) pr)

_<C'_ : CauchyCompletion → A → Set (m ⊔ o)
a <C' b = Sg A (λ ε → (0G < ε) && Sg ℕ (λ N → ((m : ℕ) → (N<m : N <N m) → (ε + index (CauchyCompletion.elts a) m) < b)))

<C'WellDefinedRight : (a : CauchyCompletion) (b c : A) → b ∼ c → a <C' b → a <C' c
<C'WellDefinedRight a b c b=c (ε , (0<e ,, (N , pr))) = ε , (0<e ,, (N , λ m N<m → <WellDefined (Equivalence.reflexive eq) b=c (pr m N<m)))

halfLess : (e/2 e : A) → (0<e : 0G < e) → (pr : e/2 + e/2 ∼ e) → e/2 < e
halfLess e/2 e 0<e pr with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr) 0<e)
... | 0<e/2 = <WellDefined identLeft pr (orderRespectsAddition 0<e/2 e/2)

<C'WellDefinedLemma : (a b e/2 e : A) (0<e : 0G < e) (pr : e/2 + e/2 ∼ e) → abs (a + inverse b) < e/2 → (e/2 + b) < (e + a)
<C'WellDefinedLemma a b e/2 e 0<e pr a-b<e with SetoidTotalOrder.totality tOrder 0G (a + inverse b)
<C'WellDefinedLemma a b e/2 e 0<e pr a-b<e | inl (inl 0<a-b) = ringAddInequalities (halfLess e/2 e 0<e pr) (<WellDefined identLeft (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) invLeft) identRight)) (orderRespectsAddition 0<a-b b))
<C'WellDefinedLemma a b e/2 e 0<e pr a-b<e | inl (inr a-b<0) = <WellDefined (Equivalence.transitive eq (+WellDefined (invContravariant (Ring.additiveGroup R)) groupIsAbelian) (Equivalence.transitive eq (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (invTwice additiveGroup b) invLeft) identRight)) (Equivalence.reflexive eq))) groupIsAbelian)) (Equivalence.transitive eq +Associative (+WellDefined pr (Equivalence.reflexive eq))) (orderRespectsAddition a-b<e (e/2 + a))
<C'WellDefinedLemma a b e/2 e 0<e pr a-b<e | inr 0=a-b = <WellDefined (Equivalence.reflexive eq) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (transferToRight (Ring.additiveGroup R) (Equivalence.symmetric eq 0=a-b)))) (orderRespectsAddition (halfLess e/2 e 0<e pr) b)

<C'WellDefinedLeft : (a b : CauchyCompletion) (c : A) → Setoid._∼_ cauchyCompletionSetoid a b → a <C' c → b <C' c
<C'WellDefinedLeft a b c a=b (ε , (0<e ,, (N , pr))) with halve charNot2 ε
... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
... | 0<e/2 with a=b e/2 0<e/2
... | N2 , prN2 = e/2 , (0<e/2 ,, ((N +N N2) , ans))
  where
    ans : (m : ℕ) → (N<m : (N +N N2) <N m) → (e/2 + index (CauchyCompletion.elts b) m) < c
    ans m N<m with prN2 {m} (shrinkInequality' N<m)
    ... | bl rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts b) inverse m) = SetoidPartialOrder.transitive pOrder (<C'WellDefinedLemma (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) e/2 ε 0<e prE/2 bl) (pr m (shrinkInequality N<m))

<C'WellDefined : (a b : CauchyCompletion) (c d : A) → Setoid._∼_ cauchyCompletionSetoid a b → c ∼ d → a <C' c → b <C' d
<C'WellDefined a b c d a=b c=d a<c = <C'WellDefinedLeft a b d a=b (<C'WellDefinedRight a c d c=d a<c)

_<C''_ : A → CauchyCompletion → Set (m ⊔ o)
a <C'' b = Sg A (λ ε → (0G < ε) && Sg ℕ (λ N → ((m : ℕ) → (N<m : N <N m) → (a + ε) < index (CauchyCompletion.elts b) m)))

<C''WellDefinedLeft : (a b : A) (c : CauchyCompletion) → (a ∼ b) → (a <C'' c) → b <C'' c
<C''WellDefinedLeft a b c a=b (e , (0<e ,, (N , pr))) = e , (0<e ,, (N , λ m N<m → <WellDefined (+WellDefined a=b (Equivalence.reflexive eq)) (Equivalence.reflexive eq) (pr m N<m)))

<C''WellDefinedLemma : (a b c e e/2 : A) (_ : e/2 + e/2 ∼ e) (0<e : 0G < e) (_ : abs (a + inverse b) < e/2) (_ : (c + e) < a) → (c + e/2) < b
<C''WellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a with SetoidTotalOrder.totality tOrder 0G (a + inverse b)
<C''WellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inl (inl 0<a-b) = SetoidPartialOrder.transitive pOrder (<WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (+WellDefined (Equivalence.symmetric eq prE/2) (Equivalence.reflexive eq)) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invRight)) identRight)))) (Equivalence.reflexive eq) (orderRespectsAddition c+e<a (inverse e/2))) (<WellDefined (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) invLeft) identRight)) (Equivalence.reflexive eq))) (Equivalence.transitive eq groupIsAbelian (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (invLeft)) identRight))) (orderRespectsAddition pr (b + inverse e/2)))
<C''WellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inl (inr a-b<0) = SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.transitive pOrder (<WellDefined groupIsAbelian groupIsAbelian (orderRespectsAddition (halfLess e/2 e 0<e prE/2) c)) c+e<a) (<WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) (+WellDefined (Equivalence.reflexive eq) invLeft)) identRight) identLeft (orderRespectsAddition a-b<0 b))
<C''WellDefinedLemma a b c e e/2 prE/2 0<e pr c+e<a | inr 0=a-b = SetoidPartialOrder.transitive pOrder (<WellDefined groupIsAbelian (Equivalence.reflexive eq) (orderRespectsAddition (halfLess e/2 e 0<e prE/2) c)) (<WellDefined (groupIsAbelian {c} {e}) (transferToRight additiveGroup (Equivalence.symmetric eq 0=a-b)) c+e<a)

<C''WellDefinedRight : (a b : CauchyCompletion) (c : A) → Setoid._∼_ cauchyCompletionSetoid a b → c <C'' a → c <C'' b
<C''WellDefinedRight a b c a=b (e , (0<e ,, (N , pr))) with halve charNot2 e
... | e/2 , prE/2 with halvePositive e/2 (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq prE/2) 0<e)
... | 0<e/2 with a=b e/2 0<e/2
... | N2 , prN2 = e/2 , (0<e/2 ,, ((N +N N2) , ans))
  where
    ans : (m : ℕ) → (N<m : (N +N N2) <N m) → (c + e/2) < index (CauchyCompletion.elts b) m
    ans m N<m with prN2 {m} (shrinkInequality' N<m)
    ... | bl rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts b) inverse m) = <C''WellDefinedLemma (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) c e e/2 prE/2 0<e bl (pr m (shrinkInequality N<m))

_<C_ : CauchyCompletion → CauchyCompletion → Set (m ⊔ o)
a <C b = Sg A (λ i → (a <C' i) && (i <C'' b))

<CWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → a <C c → b <C d
<CWellDefined {a} {b} {c} {d} a=b c=d (bound , (a<bound ,, bound<b)) = bound , (<C'WellDefinedLeft a b bound a=b a<bound ,, <C''WellDefinedRight c d bound c=d bound<b)

<C'Preserves : {a b : A} → a < b → injection a <C' b
<C'Preserves {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = (between + inverse a) , (<WellDefined invRight (Equivalence.reflexive eq) (orderRespectsAddition a<between (inverse a)) ,, (0 , λ m _ → <WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (ans a m)) +Associative)) (Equivalence.reflexive eq) between<b))
  where
    ans : (x : A) (m : ℕ) → 0G ∼ inverse x + index (constSequence x) m
    ans x m rewrite indexAndConst x m = Equivalence.symmetric eq invLeft

<C''Preserves : {a b : A} → a < b → a <C'' injection b
<C''Preserves {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = (between + inverse a) , (<WellDefined invRight (Equivalence.reflexive eq) (orderRespectsAddition a<between (inverse a)) ,, (0 , λ m _ → <WellDefined (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq invLeft))) +Associative) groupIsAbelian) (identityOfIndiscernablesLeft _∼_ (Equivalence.reflexive eq) (indexAndConst b m)) between<b))

<CInherited : {a b : A} → a < b → (injection a) <C (injection b)
<CInherited {a} {b} a<b with dense charNot2 a<b
... | between , (a<between ,, between<b) = between , (<C'Preserves a<between ,, <C''Preserves between<b)

<CInherited' : {a b : A} → (injection a) <C (injection b) → a < b
<CInherited' {a} {b} (bound , ((Na , (0<Na ,, (Na2 , prA))) ,, ((Nb , (0<Nb ,, (Nb2 , prB)))))) with prA (succ Na2) (le 0 refl)
... | bl with prB (succ Nb2) (le 0 refl)
... | bl2 rewrite indexAndConst a Na2 | indexAndConst b Nb2 = SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.transitive pOrder (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<Na a)) bl) (SetoidPartialOrder.transitive pOrder (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<Nb bound)) bl2)

<CIrreflexive : {a : CauchyCompletion} → a <C a → False
<CIrreflexive {a} (bound , ((bA , (0<bA ,, (Na , prA))) ,, ((bB , (0<bB ,, (Nb , prB)))))) with prA (succ Na +N Nb) (le Nb (applyEquality succ (Semiring.commutative ℕSemiring Nb Na)))
... | bl with prB (succ Na +N Nb) (le Na refl)
... | bl2 with <WellDefined (Equivalence.transitive eq +Associative (+WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq +Associative) groupIsAbelian) (Equivalence.reflexive eq))) groupIsAbelian (ringAddInequalities bl bl2)
... | bad = irreflexive (SetoidPartialOrder.transitive pOrder (<WellDefined identLeft +Associative (<WellDefined (Equivalence.reflexive eq) groupIsAbelian (orderRespectsAddition (<WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities 0<bA 0<bB)) (index (CauchyCompletion.elts a) (succ Na +N Nb) + bound)))) bad)

<CTransitive : {a b c : CauchyCompletion} → a <C b → b <C c → a <C c
<CTransitive {a} {b} {c} (boundA , ((eL , (0<eL ,, prL)) ,, (eR , (0<eR ,, (Nr , prR))))) (boundB , ((fL , (0<fL ,, (Nfl , prFl))) ,, (fR , (0<fR ,, (N , prFR))))) = boundA , ((eL , (0<eL ,, prL)) ,, (eR , (0<eR ,, (((Nr +N Nfl) +N N) , λ m N<m → SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.transitive pOrder (SetoidPartialOrder.transitive pOrder (prR m (shrinkInequality {Nr} (shrinkInequality N<m))) (<WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition 0<fL (index (CauchyCompletion.elts b) m)))) (prFl m (shrinkInequality' {Nr} (shrinkInequality N<m)))) (<WellDefined identLeft groupIsAbelian (orderRespectsAddition 0<fR boundB))) (prFR m (shrinkInequality' N<m))))))

<COrder : SetoidPartialOrder cauchyCompletionSetoid _<C_
SetoidPartialOrder.<WellDefined <COrder {a} {b} {c} {d} a=b c=d a<c = <CWellDefined {a} {b} {c} {d} a=b c=d a<c
SetoidPartialOrder.irreflexive <COrder {a} a<a = <CIrreflexive {a} a<a
SetoidPartialOrder.transitive <COrder {a} {b} {c} a<b b<c = <CTransitive {a} {b} {c} a<b b<c
