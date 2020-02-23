{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Functions

open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Vectors

module Logic.PropositionalLogic where

data Propositions {a : _} (primitives : Set a) : Set a where
  ofPrimitive : primitives → Propositions primitives
  false : Propositions primitives
  implies : (a b : Propositions primitives) → Propositions primitives

prNot : {a : _} {pr : Set a} → Propositions pr → Propositions pr
prNot p = implies p false

impliesIsBigger : {a : _} {pr : Set a} {P Q : Propositions pr} → Q ≡ implies P Q → False
impliesIsBigger {P = P} {Q} ()

impliesInjectiveL : {a : _} {A : Set a} → {p q r : Propositions A} → implies p q ≡ implies r q → p ≡ r
impliesInjectiveL refl = refl

impliesInjectiveR : {a : _} {A : Set a} → {p q r : Propositions A} → implies p q ≡ implies p r → q ≡ r
impliesInjectiveR refl = refl

impliesInjective : {a : _} {A : Set a} → {p q r s : Propositions A} → implies p q ≡ implies r s → (p ≡ r) && (q ≡ s)
impliesInjective refl = refl ,, refl

record Valuation {a : _} (primitives : Set a) : Set a where
  field
    v : Propositions primitives → Bool
    vFalse : v false ≡ BoolFalse
    vImplicationF : {p q : Propositions primitives} → v p ≡ BoolTrue → v q ≡ BoolFalse → v (implies p q) ≡ BoolFalse
    vImplicationVacuous : {p q : Propositions primitives} → v p ≡ BoolFalse → v (implies p q) ≡ BoolTrue
    vImplicationT : {p q : Propositions primitives} → v q ≡ BoolTrue → v (implies p q) ≡ BoolTrue

-- Proposition 1a
valuationIsDetermined : {a : _} {pr : Set a} → (v1 v2 : Valuation pr) → ({x : pr} → Valuation.v v1 (ofPrimitive x) ≡ Valuation.v v2 (ofPrimitive x)) → {x : Propositions pr} → Valuation.v v1 x ≡ Valuation.v v2 x
valuationIsDetermined v1 v2 pr {ofPrimitive x} = pr
valuationIsDetermined v1 v2 pr {false} rewrite Valuation.vFalse v1 | Valuation.vFalse v2 = refl
valuationIsDetermined v1 v2 pr {implies x y} with valuationIsDetermined v1 v2 pr {x}
valuationIsDetermined v1 v2 pr {implies x y} | eqX with valuationIsDetermined v1 v2 pr {y}
... | eqY with inspect (Valuation.v v1 x)
valuationIsDetermined v1 v2 pr {implies x y} | eqX | eqY | BoolTrue with≡ p with inspect (Valuation.v v1 y)
valuationIsDetermined v1 v2 pr {implies x y} | eqX | eqY | BoolTrue with≡ p | BoolTrue with≡ q rewrite p | q | Valuation.vImplicationT v2 {p = x} {q = y} (equalityCommutative eqY) | Valuation.vImplicationT v1 {p = x} {q = y} q = refl
valuationIsDetermined v1 v2 pr {implies x y} | eqX | eqY | BoolTrue with≡ p | BoolFalse with≡ q rewrite p | q | Valuation.vImplicationF v1 p q | Valuation.vImplicationF v2 (equalityCommutative eqX) (equalityCommutative eqY) = refl
valuationIsDetermined v1 v2 pr {implies x y} | eqX | eqY | BoolFalse with≡ p rewrite p | Valuation.vImplicationVacuous v1 {q = y} p | Valuation.vImplicationVacuous v2 {q = y} (equalityCommutative eqX) = refl

extendValuation : {a : _} {pr : Set a} → (w : pr → Bool) → Valuation pr
Valuation.v (extendValuation w) (ofPrimitive x) = w x
Valuation.v (extendValuation w) false = BoolFalse
Valuation.v (extendValuation w) (implies x y) with Valuation.v (extendValuation w) x
Valuation.v (extendValuation w) (implies x y) | BoolTrue with Valuation.v (extendValuation w) y
Valuation.v (extendValuation w) (implies x y) | BoolTrue | BoolTrue = BoolTrue
Valuation.v (extendValuation w) (implies x y) | BoolTrue | BoolFalse = BoolFalse
Valuation.v (extendValuation w) (implies x y) | BoolFalse = BoolTrue
Valuation.vFalse (extendValuation w) = refl
Valuation.vImplicationF (extendValuation w) {p} {q} pT qF with Valuation.v (extendValuation w) p
Valuation.vImplicationF (extendValuation w) {p} {q} refl qF | BoolTrue with Valuation.v (extendValuation w) q
Valuation.vImplicationF (extendValuation w) {p} {q} refl () | BoolTrue | BoolTrue
Valuation.vImplicationF (extendValuation w) {p} {q} refl refl | BoolTrue | BoolFalse = refl
Valuation.vImplicationF (extendValuation w) {p} {q} () qF | BoolFalse
Valuation.vImplicationVacuous (extendValuation w) {p} {q} pF with Valuation.v (extendValuation w) p
Valuation.vImplicationVacuous (extendValuation w) {p} {q} () | BoolTrue
Valuation.vImplicationVacuous (extendValuation w) {p} {q} refl | BoolFalse = refl
Valuation.vImplicationT (extendValuation w) {p} {q} qT with Valuation.v (extendValuation w) p
Valuation.vImplicationT (extendValuation w) {p} {q} qT | BoolTrue with Valuation.v (extendValuation w) q
Valuation.vImplicationT (extendValuation w) {p} {q} refl | BoolTrue | BoolTrue = refl
Valuation.vImplicationT (extendValuation w) {p} {q} () | BoolTrue | BoolFalse
Valuation.vImplicationT (extendValuation w) {p} {q} qT | BoolFalse = refl

-- Proposition 1b
valuationsAreFree : {a : _} {pr : Set a} → (w : pr → Bool) → {x : pr} → Valuation.v (extendValuation w) (ofPrimitive x) ≡ w x
valuationsAreFree w = refl

Tautology : {a : _} {pr : Set a} (prop : Propositions pr) → Set a
Tautology {pr = pr} prop = {v : Valuation pr} → Valuation.v v prop ≡ BoolTrue

record IsSubset {a b : _} (sub : Set a) (super : Set b) : Set (a ⊔ b) where
  field
    ofElt : sub → super

mapProp : {a b : _} {pr1 : Set a} {pr2 : Set b} → (pr1 → pr2) → Propositions pr1 → Propositions pr2
mapProp f (ofPrimitive x) = ofPrimitive (f x)
mapProp f false = false
mapProp f (implies p q) = implies (mapProp f p) (mapProp f q)

inheritedValuation : {a b : _} {sub : Set a} {super : Set b} → (IsSubset sub super) → Valuation super → Valuation sub
Valuation.v (inheritedValuation isSub v) prop = Valuation.v v (mapProp (IsSubset.ofElt isSub) prop)
Valuation.vFalse (inheritedValuation isSub v) = Valuation.vFalse v
Valuation.vImplicationF (inheritedValuation isSub v) pT qF = Valuation.vImplicationF v pT qF
Valuation.vImplicationVacuous (inheritedValuation isSub v) pF = Valuation.vImplicationVacuous v pF
Valuation.vImplicationT (inheritedValuation isSub v) qT = Valuation.vImplicationT v qT

inheritedValuation' : {a b : _} {sub : Set a} {super : Set b} → (IsSubset sub (Propositions super)) → Valuation super → (x : sub) → Bool
inheritedValuation' subset v x = Valuation.v v (IsSubset.ofElt subset x)

record Entails {a b : _} {sub : Set a} {super : Set b} (S : IsSubset sub (Propositions super)) (P : Propositions super) : Set (a ⊔ b) where
  field
    entails : {v : Valuation super} → ({s : sub} → inheritedValuation' S v s ≡ BoolTrue) → Valuation.v v P ≡ BoolTrue

data ThreeElements : Set where
  One : ThreeElements
  Two : ThreeElements
  Three : ThreeElements

indexAxiom : {a : _} (A : Set a) → ThreeElements → Set a
indexAxiom A One = Propositions A && Propositions A
indexAxiom A Two = Propositions A & Propositions A & Propositions A
indexAxiom A Three = Propositions A

indexPropositionalAxioms : {a : _} {A : Set a} → Set a
indexPropositionalAxioms {A = A} = Sg ThreeElements (indexAxiom A)

-- An axiom system is simply a subset of a set of propositions.
propositionalAxioms : {a : _} {A : Set a} → IsSubset (indexPropositionalAxioms {A = A}) (Propositions A)
IsSubset.ofElt propositionalAxioms (One , (p ,, q)) = implies p (implies q p)
IsSubset.ofElt propositionalAxioms (Two , record { one = p ; two = q ; three = r }) = implies (implies p (implies q r)) (implies (implies p q) (implies p r))
IsSubset.ofElt propositionalAxioms (Three , p) = implies (prNot (prNot p)) p

record Selection {a : _} {A : Set a} {n : ℕ} (l : Vec A n) : Set a where
  field
    element : A
    position : ℕ
    pos<N : position <N n
    elementIsAt : vecIndex l position pos<N ≡ element

data Proof {a b c : _} {A : Set a} {axioms : Set b} (axiomsSubset : IsSubset axioms (Propositions A)) {givens : Set c} (givensSubset : IsSubset givens (Propositions A)) : (n : ℕ) → Set (a ⊔ b ⊔ c)
data ProofStep {a b c : _} {A : Set a} {axioms : Set b} (axiomsSubset : IsSubset axioms (Propositions A)) {givens : Set c} (givensSubset : IsSubset givens (Propositions A)) {n : ℕ} (proofSoFar : Proof {a} {b} {c} {A} {axioms} axiomsSubset {givens} givensSubset n) : Set (a ⊔ b ⊔ c)

toSteps : {a b c : _} {A : Set a} {axioms : Set b} {axiomsSubset : IsSubset axioms (Propositions A)} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} {n : ℕ} (pr : Proof {axioms = axioms} axiomsSubset {givens = givens} givensSubset n) → Vec (Propositions A) n

data ProofStep {a} {b} {c} {A} {axioms} axiomsSubset {givens} givensSubset proofSoFar where
  axiom : axioms → ProofStep axiomsSubset givensSubset proofSoFar
  given : givens → ProofStep axiomsSubset givensSubset proofSoFar
  modusPonens : (implication : Selection (toSteps proofSoFar)) → (argument : Selection (toSteps proofSoFar)) → (conclusion : Propositions A) → (Selection.element implication ≡ implies (Selection.element argument) conclusion) → ProofStep axiomsSubset givensSubset proofSoFar
data Proof {a} {b} {c} {A} {axioms} axiomsSubset {givens} givensSubset where
  empty : Proof axiomsSubset givensSubset 0
  nextStep : (n : ℕ) → (previous : Proof {axioms = axioms} axiomsSubset {givens = givens} givensSubset n) → ProofStep axiomsSubset givensSubset previous → Proof axiomsSubset givensSubset (succ n)

toSteps empty = []
toSteps {axiomsSubset = axiomsSubset} (nextStep n pr (axiom x)) = (IsSubset.ofElt axiomsSubset x) ,- toSteps pr
toSteps {givensSubset = givensSubset} (nextStep n pr (given x)) = IsSubset.ofElt givensSubset x ,- toSteps pr
toSteps (nextStep n pr (modusPonens implication argument conclusion x)) = conclusion ,- toSteps pr

record Proves {a b c : _} {A : Set a} {axioms : Set b} (axiomsSubset : IsSubset axioms (Propositions A)) {givens : Set c} (givensSubset : IsSubset givens (Propositions A)) (P : Propositions A) : Set (a ⊔ b ⊔ c) where
  field
    n : ℕ
    proof : Proof axiomsSubset givensSubset (succ n)
    ofStatement : vecIndex (toSteps proof) 0 (succIsPositive n) ≡ P

addSingletonSet : {a : _} → Set a → Set a
addSingletonSet A = True || A

interpretSingletonSet : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → IsSubset A B → (c : C) → (addSingletonSet A) → C || B
interpretSingletonSet A<B c (inl x) = inl c
interpretSingletonSet A<B _ (inr x) = inr (IsSubset.ofElt A<B x)

inrInjective : {a b : _} {A : Set a} {B : Set b} {b1 b2 : B} → inr {a = a} {A = A} b1 ≡ inr b2 → b1 ≡ b2
inrInjective refl = refl

singletonSubset : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → IsSubset A B → (c : C) → IsSubset (addSingletonSet A) (C || B)
IsSubset.ofElt (singletonSubset subs c) = interpretSingletonSet subs c

adjoinGiven : {a b : _} {A : Set a} {givens : Set b} (givensSubset : IsSubset givens A) (P : A) → IsSubset (addSingletonSet givens) A
IsSubset.ofElt (adjoinGiven record { ofElt = ofElt } P) (inl x) = P
IsSubset.ofElt (adjoinGiven record { ofElt = ofElt } _) (inr x) = ofElt x

{-
proofRemainsValidOnAddingGivens : {a b c : _} {A : Set a} {axioms : Set b} {axiomsSubset : IsSubset axioms (Propositions A)} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} {n : ℕ} → {Q : Propositions A} → Proof axiomsSubset givensSubset n → Proof axiomsSubset (adjoinGiven givensSubset Q) n
pr' : {a b c : _} {A : Set a} {axioms : Set b} {axiomsSubset : IsSubset axioms (Propositions A)} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} {n : ℕ} → {Q : Propositions A} → (pr : Proof axiomsSubset givensSubset n) → toSteps pr ≡ toSteps (proofRemainsValidOnAddingGivens {Q = Q} pr)

proofRemainsValidOnAddingGivens {Q = Q} empty = empty
proofRemainsValidOnAddingGivens {Q = Q} (nextStep n pr (axiom x)) = nextStep n (proofRemainsValidOnAddingGivens pr) (axiom x)
proofRemainsValidOnAddingGivens {Q = Q} (nextStep n pr (given x)) = nextStep n (proofRemainsValidOnAddingGivens pr) (given (inr x))
proofRemainsValidOnAddingGivens {A = A} {axiomsSubset = axiomsSubset} {givensSubset = givensSubset} {Q = Q} (nextStep n pr (modusPonens implication argument conclusion x)) = nextStep n (proofRemainsValidOnAddingGivens pr) (modusPonens (record { element = Selection.element implication ; position = Selection.position implication ; pos<N = Selection.pos<N implication ; elementIsAt = lemma implication }) (record { element = Selection.element argument ; position = Selection.position argument ; pos<N = Selection.pos<N argument ; elementIsAt = lemma argument }) conclusion x)
  where
    lemma : (sel : Selection (toSteps pr)) → vecIndex (toSteps (proofRemainsValidOnAddingGivens pr)) (Selection.position sel) (Selection.pos<N sel) ≡ Selection.element sel
    lemma sel = {!!}

pr' empty = refl
pr' (nextStep n pr (axiom x)) rewrite pr' pr = refl
pr' (nextStep n pr (given x)) rewrite pr' pr = refl
pr' (nextStep n pr (modusPonens implication argument conclusion x)) rewrite pr' pr = refl

vecIndexRefl : {a : _} {A : Set a} {n : ℕ} {v1 v2 : Vec A n} → {pos : ℕ} → {pos<N1 pos<N2 : pos <N n} → v1 ≡ v2 → vecIndex v1 pos pos<N1 ≡ vecIndex v2 pos pos<N2
vecIndexRefl {v1 = v1} {.v1} {pos} {pos<N1} {pos<N2} refl rewrite <NRefl pos<N1 pos<N2 = refl

proofImpliesProves : {a b c : _} {A : Set a} {axioms : Set b} {axiomsSubset : IsSubset axioms (Propositions A)} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} {n : ℕ} (0<n : 0 <N n) → (p : Proof axiomsSubset givensSubset n) → (pr : Propositions A) → vecIndex (toSteps p) 0 0<n ≡ pr → Proves axiomsSubset givensSubset pr
proofImpliesProves {n = zero} () p pr x
proofImpliesProves {n = succ n} _ p pr x = record { n = n ; proof = p ; ofStatement = transitivity (vecIndexRefl {v1 = toSteps p} refl) x }

deductionTheorem' : {a b c : _} {A : Set a} {axioms : Set b} {axiomsSubset : IsSubset axioms (Propositions A)} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} {n : ℕ} → {P Q : Propositions A} → Proves axiomsSubset givensSubset (implies P Q) → Proves axiomsSubset {givens = addSingletonSet givens} (adjoinGiven givensSubset P) Q
Proves.n (deductionTheorem' record { n = n ; proof = proof ; ofStatement = ofStatement }) = succ (succ n)
Proves.proof (deductionTheorem' {P = P} {Q = Q} record { n = n ; proof = proof ; ofStatement = ofStatement }) = nextStep (succ (succ n)) (nextStep (succ n) (proofRemainsValidOnAddingGivens proof) (given (inl record {}))) (modusPonens (record { element = implies P Q ; position = 1 ; pos<N = succPreservesInequality (succIsPositive _) ; elementIsAt = transitivity (equalityCommutative (vecIndexRefl (pr' proof))) ofStatement }) (record { element = P ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) Q refl)
Proves.ofStatement (deductionTheorem' record { n = n ; proof = proof ; ofStatement = ofStatement }) = refl

deductionTheorem : {a b c : _} {A : Set a} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} {n : ℕ} → {P Q : Propositions A} → Proves propositionalAxioms {givens = addSingletonSet givens} (adjoinGiven givensSubset P) Q → Proves propositionalAxioms givensSubset (implies P Q)
deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (axiom x)) ; ofStatement = ofStatement } = {!!}
--... | bl = record { n = {!!} ; proof = nextStep (succ (succ (succ n))) (nextStep (succ (succ n)) (nextStep (succ n) {!deductionTheorem proof!} (axiom x)) (axiom (One , (Q ,, P)))) (modusPonens (record { element = implies Q (implies P Q) ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) (record { element = Q ; position = 1 ; pos<N = succPreservesInequality (succIsPositive _) ; elementIsAt = ofStatement }) (implies P Q) refl) ; ofStatement = {!!} }
deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (given x)) ; ofStatement = ofStatement } = {!!}
deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (modusPonens implication argument conclusion x)) ; ofStatement = ofStatement } = {!!}
{-
Proves.n (deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (axiom x)) ; ofStatement = ofStatement }) = succ (succ (succ n))
Proves.proof (deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (axiom x)) ; ofStatement = ofStatement }) = nextStep (succ (succ (succ n))) (nextStep (succ (succ n)) (nextStep (succ n) {!!} (axiom x)) (axiom (One , (Q ,, P)))) (modusPonens (record { element = implies Q (implies P Q) ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) (record { element = Q ; position = 1 ; pos<N = succPreservesInequality (succIsPositive _) ; elementIsAt = ofStatement }) (implies P Q) refl)
Proves.ofStatement (deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (axiom x)) ; ofStatement = ofStatement }) = {!!}
deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (given x)) ; ofStatement = ofStatement } = {!!}
deductionTheorem {P = P} {Q} record { n = n ; proof = (nextStep .n proof (modusPonens implication argument conclusion x)) ; ofStatement = ofStatement } = {!!}

-}

axiomKTaut : {a : _} {A : Set a} {P Q : Propositions A} → Tautology (implies P (implies Q P))
Tautology.isTaut (axiomKTaut {P = P} {Q}) {v = v} with inspect (Valuation.v v P)
Tautology.isTaut (axiomKTaut {P = P} {Q}) {v} | BoolTrue with≡ pT with inspect (Valuation.v v Q)
Tautology.isTaut (axiomKTaut {P = P} {Q}) {v} | BoolTrue with≡ pT | BoolTrue with≡ qT = Valuation.vImplicationT v (Valuation.vImplicationT v pT)
Tautology.isTaut (axiomKTaut {P = P} {Q}) {v} | BoolTrue with≡ pT | BoolFalse with≡ qF = Valuation.vImplicationT v (Valuation.vImplicationVacuous v qF)
Tautology.isTaut (axiomKTaut {P = P} {Q}) {v} | BoolFalse with≡ pF = Valuation.vImplicationVacuous v pF

excludedMiddleTaut : {a : _} {A : Set a} {P : Propositions A} → Tautology (implies (prNot (prNot P)) P)
Tautology.isTaut (excludedMiddleTaut {P = P}) {v} with inspect (Valuation.v v P)
Tautology.isTaut (excludedMiddleTaut {P = P}) {v} | BoolTrue with≡ pT = Valuation.vImplicationT v pT
Tautology.isTaut (excludedMiddleTaut {P = P}) {v} | BoolFalse with≡ pF = Valuation.vImplicationVacuous v (Valuation.vImplicationF v (Valuation.vImplicationVacuous v pF) (Valuation.vFalse v))

axiomSTaut : {a : _} {A : Set a} {P Q R : Propositions A} → Tautology (implies (implies P (implies Q R)) (implies (implies P Q) (implies P R)))
Tautology.isTaut (axiomSTaut {P = P} {Q} {R}) {v} with inspect (Valuation.v v P)
Tautology.isTaut (axiomSTaut {P = P} {Q} {R}) {v} | BoolTrue with≡ pT with inspect (Valuation.v v Q)
Tautology.isTaut (axiomSTaut {P = P} {Q} {R}) {v} | BoolTrue with≡ pT | BoolTrue with≡ qT with inspect (Valuation.v v R)
Tautology.isTaut (axiomSTaut {P = P} {Q} {R}) {v} | BoolTrue with≡ pT | BoolTrue with≡ qT | BoolTrue with≡ rT = Valuation.vImplicationT v (Valuation.vImplicationT v (Valuation.vImplicationT v rT))
Tautology.isTaut (axiomSTaut {P = P} {Q} {R}) {v} | BoolTrue with≡ pT | BoolTrue with≡ qT | BoolFalse with≡ rF = Valuation.vImplicationVacuous v (Valuation.vImplicationF v pT (Valuation.vImplicationF v qT rF))
Tautology.isTaut (axiomSTaut {P = P} {Q} {R}) {v} | BoolTrue with≡ pT | BoolFalse with≡ qF = Valuation.vImplicationT v (Valuation.vImplicationVacuous v (Valuation.vImplicationF v pT qF))
Tautology.isTaut (axiomSTaut {P = P} {Q} {R}) {v} | BoolFalse with≡ pF = Valuation.vImplicationT v (Valuation.vImplicationT v (Valuation.vImplicationVacuous v pF))


propositionalAxiomsTautology : {a : _} {A : Set a} (x : Sg ThreeElements (indexAxiom A)) → Tautology (IsSubset.ofElt propositionalAxioms x)
propositionalAxiomsTautology (One , (fst ,, snd)) = axiomKTaut
propositionalAxiomsTautology (Two , record { one = one ; two = two ; three = three }) = axiomSTaut
propositionalAxiomsTautology (Three , b) = excludedMiddleTaut

propositionalLogicSound : {a b c : _} {A : Set a} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} → {P : Propositions A} → Proves propositionalAxioms givensSubset P → Entails givensSubset P
Entails.entails (propositionalLogicSound {P = .(IsSubset.ofElt propositionalAxioms x)} record { n = .0 ; proof = (nextStep .0 empty (axiom x)) ; ofStatement = refl }) {v} values = Tautology.isTaut (propositionalAxiomsTautology x) {v}
Entails.entails (propositionalLogicSound {P = P} record { n = .0 ; proof = (nextStep .0 empty (given x)) ; ofStatement = ofStatement }) {v} values rewrite equalityCommutative ofStatement = values {x}
Entails.entails (propositionalLogicSound {P = P} record { n = .0 ; proof = (nextStep .0 empty (modusPonens record { element = element ; position = zero ; pos<N = (le x₁ ()) ; elementIsAt = elementIsAt } argument conclusion x)) ; ofStatement = ofStatement }) {v} values
Entails.entails (propositionalLogicSound {P = P} record { n = .0 ; proof = (nextStep .0 empty (modusPonens record { element = element ; position = (succ position) ; pos<N = (le x₁ ()) ; elementIsAt = elementIsAt } argument conclusion x)) ; ofStatement = ofStatement }) {v} values
Entails.entails (propositionalLogicSound {P = P} record { n = .(succ n) ; proof = (nextStep .(succ n) (nextStep n proof y) x) ; ofStatement = ofStatement }) {v} values = {!!}

-}
