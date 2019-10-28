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

module Fields.CauchyCompletion.Multiplication {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder {_<_ = _<_} pOrder} {R : Ring S _+_ _*_} (order : OrderedRing R tOrder) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder tOrder
open SetoidPartialOrder pOrder
open Equivalence eq
open OrderedRing order
open Ring R
open Group additiveGroup
open Field F

open import Rings.Orders.Lemmas(order)
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Setoid order F charNot2
open import Fields.CauchyCompletion.Comparison order F charNot2
open import Fields.CauchyCompletion.Addition order F charNot2
open import Fields.CauchyCompletion.Approximation order F charNot2

_*C_ : CauchyCompletion → CauchyCompletion → CauchyCompletion
CauchyCompletion.elts (record { elts = a ; converges = aConv } *C record { elts = b ; converges = bConv }) = apply _*_ a b
CauchyCompletion.converges (record { elts = a ; converges = aConv } *C record { elts = b ; converges = bConv }) ε 0<e = {!!}

*CCommutative : {a b : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a *C b) (b *C a)
*CCommutative {a} {b} ε 0<e = 0 , ans
  where
    foo : {x y : A} → (x * y) + inverse (y * x) ∼ 0G
    foo = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (inverseWellDefined additiveGroup *Commutative)) invRight
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (a *C b)) (map inverse (CauchyCompletion.elts (b *C a)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts a))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _*_ {m} | equalityCommutative (mapAndIndex (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts a)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts a) _*_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ foo) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) (absZero order)))) (Equivalence.reflexive eq) 0<e

absBoundedImpliesBounded : {a b : A} → abs a < b → a < b
absBoundedImpliesBounded {a} {b} a<b with SetoidTotalOrder.totality tOrder 0G a
absBoundedImpliesBounded {a} {b} a<b | inl (inl x) = a<b
absBoundedImpliesBounded {a} {b} a<b | inl (inr x) = SetoidPartialOrder.transitive pOrder x (SetoidPartialOrder.transitive pOrder (lemm2 a x) a<b)
absBoundedImpliesBounded {a} {b} a<b | inr x = a<b

multiplicationWellDefinedLeft' : (0!=1 : 0R ∼ 1R → False) (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C c)
multiplicationWellDefinedLeft' 0!=1 a b c a=b ε 0<e = N , ans
  where
    cBoundAndPr : Sg A (λ b → Sg ℕ (λ N → (m : ℕ) → (N <N m) → (abs (index (CauchyCompletion.elts c) m)) < b))
    cBoundAndPr = boundModulus 0!=1 c
    cBound : A
    cBound with cBoundAndPr
    ... | a , _ = a
    cBoundN : ℕ
    cBoundN with cBoundAndPr
    ... | _ , (N , _) = N
    cBoundPr : (m : ℕ) → (cBoundN <N m) → (abs (index (CauchyCompletion.elts c) m)) < cBound
    cBoundPr with cBoundAndPr
    ... | _ , (_ , pr) = pr
    0<cBound : 0G < cBound
    0<cBound with totality 0G cBound
    0<cBound | inl (inl 0<cBound) = 0<cBound
    0<cBound | inl (inr cBound<0) = exFalso (absNonnegative (SetoidPartialOrder.transitive pOrder (cBoundPr (succ cBoundN) (le 0 refl)) cBound<0))
    0<cBound | inr 0=cBound = exFalso (absNonnegative (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=cBound) (cBoundPr (succ cBoundN) (le 0 refl))))
    e/c : A
    e/c with allInvertible cBound (λ pr → irreflexive (<WellDefined (Equivalence.reflexive eq) pr 0<cBound))
    ... | (1/c , _) = ε * 1/c
    e/cPr : e/c * cBound ∼ ε
    e/cPr with allInvertible cBound (λ pr → irreflexive (<WellDefined (Equivalence.reflexive eq) pr 0<cBound))
    ... | (1/c , pr) = Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq *Associative) (*WellDefined (Equivalence.reflexive eq) pr)) *Commutative) (identIsIdent)
    0<e/c : 0G < e/c
    0<e/c = ringCanCancelPositive {0G} {e/c} 0<cBound (<WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative timesZero)) (Equivalence.symmetric eq e/cPr) 0<e)
    abBound : ℕ
    abBound with a=b e/c 0<e/c
    ... | Na=b , _ = Na=b
    abPr : {m : ℕ} → (abBound <N m) → abs (index (apply _+_ (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b))) m) < e/c
    abPr with a=b e/c 0<e/c
    ... | Na=b , pr = pr
    N : ℕ
    N = abBound +N cBoundN
    cBounded : (m : ℕ) → (N <N m) → abs (index (CauchyCompletion.elts c) m) < cBound
    cBounded m N<m = cBoundPr m (inequalityShrinkRight N<m)
    a-bSmall : (m : ℕ) → N <N m → abs ((index (CauchyCompletion.elts a) m) + inverse (index (CauchyCompletion.elts b) m)) < e/c
    a-bSmall m N<m with abPr {m} (inequalityShrinkLeft N<m)
    ... | f rewrite indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m} | equalityCommutative (mapAndIndex (CauchyCompletion.elts b) inverse m) = f
    ans : {m : ℕ} → N <N m → abs (index (apply _+_ (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts c)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)))) m) < ε
    ans {m} N<m rewrite indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts c)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c))) _+_ {m} | equalityCommutative (mapAndIndex (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts c) _*_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts c) _*_ {m} = <WellDefined (absWellDefined _ _ (+WellDefined (Equivalence.reflexive eq) (ringMinusExtracts' R))) (Equivalence.reflexive eq) (<WellDefined (absWellDefined ((index (CauchyCompletion.elts a) m + inverse (index (CauchyCompletion.elts b) m)) * index (CauchyCompletion.elts c) m) _ (Equivalence.transitive eq (Equivalence.transitive eq *Commutative *DistributesOver+) (+WellDefined *Commutative *Commutative))) (Equivalence.reflexive eq) (<WellDefined (Equivalence.symmetric eq (absRespectsTimes _ _)) (Equivalence.reflexive eq) (<WellDefined (Equivalence.reflexive eq) e/cPr (ans' (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) (index (CauchyCompletion.elts c) m) (a-bSmall m N<m) (cBounded m N<m)))))
      where
        ans' : (a b c : A) → abs (a + inverse b) < e/c → abs c < cBound → (abs (a + inverse b) * abs c) < (e/c * cBound)
        ans' a b c a-b<e/c c<bound with SetoidTotalOrder.totality tOrder 0R c
        ans' a b c a-b<e/c c<bound | inl (inl 0<c) with totality 0G (a + inverse b)
        ans' a b c a-b<e/c c<bound | inl (inl 0<c) | inl (inl 0<a-b) = ringMultiplyPositives 0<a-b 0<c a-b<e/c c<bound
        ans' a b c a-b<e/c c<bound | inl (inl 0<c) | inl (inr a-b<0) = ringMultiplyPositives (lemm2 (a + inverse b) a-b<0) 0<c a-b<e/c c<bound
        ans' a b c a-b<e/c c<bound | inl (inl 0<c) | inr 0=a-b = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a-b) (Equivalence.reflexive eq)) (Equivalence.transitive eq *Commutative timesZero))) (Equivalence.reflexive eq) (orderRespectsMultiplication 0<e/c 0<cBound)
        ans' a b c a-b<e/c c<bound | inl (inr c<0) with totality 0G (a + inverse b)
        ans' a b c a-b<e/c c<bound | inl (inr c<0) | inl (inl 0<a-b) = ringMultiplyPositives 0<a-b (lemm2 c c<0) a-b<e/c c<bound
        ans' a b c a-b<e/c c<bound | inl (inr c<0) | inl (inr a-b<0) = ringMultiplyPositives (lemm2 (a + inverse b) a-b<0) (lemm2 c c<0) a-b<e/c c<bound
        ans' a b c a-b<e/c c<bound | inl (inr c<0) | inr 0=a-b = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a-b) (Equivalence.reflexive eq)) (Equivalence.transitive eq *Commutative timesZero))) (Equivalence.reflexive eq) (orderRespectsMultiplication 0<e/c 0<cBound)
        ans' a b c a-b<e/c c<bound | inr 0=c = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=c)) timesZero)) (Equivalence.reflexive eq) (orderRespectsMultiplication 0<e/c 0<cBound)


multiplicationWellDefinedLeft : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C c)
multiplicationWellDefinedLeft with SetoidTotalOrder.totality tOrder 0R 1R
... | inl (inl 0<1') = multiplicationWellDefinedLeft' (λ pr → irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr) 0<1'))
... | inl (inr 1<0) = multiplicationWellDefinedLeft' (λ pr → irreflexive {0G} (<WellDefined (Equivalence.symmetric eq pr) (Equivalence.reflexive eq) 1<0))
... | inr (0=1) = λ a b c a=b → Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C c} {injection 0G} {b *C c} (Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {injection 0G} {a *C c} (trivialIfInputTrivial 0=1 (a *C c))) (trivialIfInputTrivial 0=1 (b *C c))

multiplicationPreservedLeft : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (injection a *C c) (injection b *C c)
multiplicationPreservedLeft {a} {b} {c} a=b = multiplicationWellDefinedLeft (injection a) (injection b) c (injectionPreservesSetoid a b a=b)

multiplicationPreservedRight : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (c *C injection a) (c *C injection b)
multiplicationPreservedRight {a} {b} {c} a=b = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {c *C injection a} {injection a *C c} {c *C injection b} (*CCommutative {c} {injection a}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a *C c} {injection b *C c} {c *C injection b} (multiplicationPreservedLeft {a} {b} {c} a=b) (*CCommutative {injection b} {c}))

multiplicationPreserved : {a b c d : A} → (a ∼ b) → (c ∼ d) → Setoid._∼_ cauchyCompletionSetoid (injection a *C injection c) (injection b *C injection d)
multiplicationPreserved {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a *C injection c} {injection a *C injection d} {injection b *C injection d} (multiplicationPreservedRight {c} {d} {injection a} c=d) (multiplicationPreservedLeft {a} {b} {injection d} a=b)

multiplicationWellDefinedRight : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid b c → Setoid._∼_ cauchyCompletionSetoid (a *C b) (a *C c)
multiplicationWellDefinedRight a b c b=c = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C b} {b *C a} {a *C c} (*CCommutative {a} {b}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {b *C a} {c *C a} {a *C c} (multiplicationWellDefinedLeft b c a b=c) (*CCommutative {c} {a}))

multiplicationWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C d)
multiplicationWellDefined {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C c} {a *C d} {b *C d} (multiplicationWellDefinedRight a c d c=d) (multiplicationWellDefinedLeft a b d a=b)
