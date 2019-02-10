{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Functions

open import Numbers.Naturals
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

record Tautology {a : _} {pr : Set a} (prop : Propositions pr) : Set a where
  field
    isTaut : {v : Valuation pr} → Valuation.v v prop ≡ BoolTrue

record IsSubset {a b : _} (sub : Set a) (super : Set b) : Set (a ⊔ b) where
  field
    ofElt : sub → super
    inj : Injection ofElt

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
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {One , (a ,, b)} pr with impliesInjective pr
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {One , (a ,, b)} pr | fst ,, snd with impliesInjective snd
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {One , (a ,, b)} pr | p=a ,, _ | q=b ,, _ rewrite p=a | q=b = refl
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {Two , record { one = a ; two = b ; three = c }} pr with impliesInjective pr
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {Two , record { one = a ; two = b ; three = c }} pr | fst ,, snd with impliesInjective snd
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {Two , record { one = a ; two = b ; three = c }} pr | p=a-b-c ,, _ | q=a-b ,, p=a-c with impliesInjective (transitivity (equalityCommutative p=a-c) p=a-b-c)
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {Two , record { one = a ; two = b ; three = c }} pr | p=a-b-c ,, _ | q=a-b ,, p=a-c | _ ,, c=b->c = exFalso (impliesIsBigger c=b->c)
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {Three , b} pr with impliesInjective pr
Injection.property (IsSubset.inj propositionalAxioms) {One , (p ,, q)} {Three , b} pr | p=nnb ,, q-p=b rewrite equalityCommutative q-p=b = exFalso (d pr)
  where
    d : _ → _
    d ()
Injection.property (IsSubset.inj propositionalAxioms) {Two , record { one = p ; two = q ; three = r }} {One , (fst ,, snd)} ()
Injection.property (IsSubset.inj propositionalAxioms) {Two , record { one = p ; two = q ; three = r }} {Two , record { one = one ; two = two ; three = three }} pr with impliesInjective pr
Injection.property (IsSubset.inj propositionalAxioms) {Two , record { one = p ; two = q ; three = r }} {Two , record { one = one ; two = two ; three = three }} pr | fst ,, snd with impliesInjective fst
Injection.property (IsSubset.inj propositionalAxioms) {Two , record { one = p ; two = q ; three = r }} {Two , record { one = one ; two = two ; three = three }} pr | _ ,, snd | p=one ,, snd1 with impliesInjective snd1
Injection.property (IsSubset.inj propositionalAxioms) {Two , record { one = p ; two = q ; three = r }} {Two , record { one = one ; two = two ; three = three }} pr | _ ,, snd | p=one ,, _ | q=two ,, r=three rewrite p=one | q=two | r=three = refl
Injection.property (IsSubset.inj propositionalAxioms) {Two , record { one = p ; two = q ; three = r }} {Three , b} ()
Injection.property (IsSubset.inj propositionalAxioms) {Three , p} {One , (a ,, b)} pr with impliesInjective pr
Injection.property (IsSubset.inj propositionalAxioms) {Three , p} {One , (a ,, b)} () | nnp=a ,, p=b-a
Injection.property (IsSubset.inj propositionalAxioms) {Three , p} {Two , record { one = a ; two = b ; three = c }} ()
Injection.property (IsSubset.inj propositionalAxioms) {Three , p} {Three , b} pr rewrite _&&_.snd (impliesInjective pr) = refl

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
Injection.property (IsSubset.inj (singletonSubset subs c)) {inl record {}} {inl record {}} px=py = refl
Injection.property (IsSubset.inj (singletonSubset subs c)) {inl record {}} {inr y} ()
Injection.property (IsSubset.inj (singletonSubset subs c)) {inr x} {inl record {}} ()
Injection.property (IsSubset.inj (singletonSubset subs c)) {inr x} {inr y} px=py rewrite Injection.property (IsSubset.inj subs) {x} {y} (inrInjective px=py) = refl

deductionTheorem' : {a b c : _} {A : Set a} {axioms : Set b} {axiomsSubset : IsSubset axioms (Propositions A)} {givens : Set c} {givensSubset : IsSubset givens (Propositions A)} {n : ℕ} → {P Q : Propositions A} → Proves axiomsSubset {givens = addSingletonSet givens} {!singletonSubset givensSubset ?!} Q → Proves axiomsSubset givensSubset (implies P Q)
deductionTheorem' = {!!}
