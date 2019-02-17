{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Logic.PropositionalLogic
open import Functions
open import Numbers.Naturals
open import Vectors

module Logic.PropositionalLogicExamples where

emptySubset : {a : _} (A : Set a) → IsSubset False A
emptySubset A = record { ofElt = λ () }

emptyEntailment : {a b : _} {A : Set a} {P : Propositions A} → Entails (emptySubset (Propositions A)) P → Tautology P
Tautology.isTaut (emptyEntailment {a} {b} {A} {P} record { entails = entails }) {v} = entails {v} λ {s} → exFalso s

emptyEntailment' : {a b : _} {A : Set a} {P : Propositions A} → Tautology P → Entails (emptySubset (Propositions A)) P
Entails.entails (emptyEntailment' record { isTaut = isTaut }) {v} _ = isTaut {v}

data TwoElements : Set where
  One : TwoElements
  Two : TwoElements

twoElementSubset : {a : _} {A : Set a} → {P Q R : Propositions A} → TwoElements → Propositions A
twoElementSubset {P = P} {Q} {R} One = implies P Q
twoElementSubset {P = P} {Q} {R} Two = implies Q R

twoElementSubsetInj : {a : _} {A : Set a} {P Q R : Propositions A} → (P ≡ Q → False) → Injection (twoElementSubset {P = P} {Q} {R})
Injection.property (twoElementSubsetInj {P = P} {Q} {R} p!=q) {One} {One} refl = refl
Injection.property (twoElementSubsetInj {P = P} {Q} {R} p!=q) {One} {Two} pr with impliesInjective pr
Injection.property (twoElementSubsetInj {P = P} {Q} {R} p!=q) {One} {Two} pr | fst ,, snd = exFalso (p!=q fst)
Injection.property (twoElementSubsetInj {P = P} {Q} {R} p!=q) {Two} {One} pr with impliesInjective pr
Injection.property (twoElementSubsetInj {P = P} {Q} {R} p!=q) {Two} {One} pr | fst ,, snd = exFalso (p!=q (equalityCommutative fst))
Injection.property (twoElementSubsetInj {P = P} {Q} {R} p!=q) {Two} {Two} refl = refl

badBool : BoolFalse ≡ BoolTrue → False
badBool ()

semanticEntailmentTransitive : {a : _} {A : Set a} {P Q R : Propositions A} → (p!=q : P ≡ Q → False) → Entails record { ofElt = twoElementSubset } (implies P R)
Entails.entails (semanticEntailmentTransitive {P = P} {Q} {R} p!=q) {v} pr with inspect (Valuation.v v P)
Entails.entails (semanticEntailmentTransitive {P = P} {Q} {R} p!=q) {v} pr | BoolTrue with≡ pT with inspect (Valuation.v v Q)
Entails.entails (semanticEntailmentTransitive {P = P} {Q} {R} p!=q) {v} pr | BoolTrue with≡ pT | BoolTrue with≡ qT with inspect (Valuation.v v R)
Entails.entails (semanticEntailmentTransitive {P = P} {Q} {R} p!=q) {v} pr | BoolTrue with≡ pT | BoolTrue with≡ qT | BoolTrue with≡ rT = Valuation.vImplicationT v rT
Entails.entails (semanticEntailmentTransitive {P = P} {Q} {R} p!=q) {v} pr | BoolTrue with≡ pT | BoolTrue with≡ qT | BoolFalse with≡ rF = exFalso (badBool (transitivity (equalityCommutative (Valuation.vImplicationF v qT rF)) (pr {Two})))
Entails.entails (semanticEntailmentTransitive {P = P} {Q} {R} p!=q) {v} pr | BoolTrue with≡ pT | BoolFalse with≡ qF = exFalso (badBool (transitivity (equalityCommutative (Valuation.vImplicationF v pT qF)) (pr {One})))
Entails.entails (semanticEntailmentTransitive {P = P} {Q} {R} p!=q) {v} pr | BoolFalse with≡ pF = Valuation.vImplicationVacuous v pF

-- Subset {p -> q, q -> r}
pQQR : {a : _} {A : Set a} {P Q R : Propositions A} → TwoElements → Propositions A
pQQR {P = P} {Q} {R} One = implies P Q
pQQR {P = P} {Q} {R} Two = implies Q R

pQQRSubsetInj : {a : _} {A : Set a} {P Q R : Propositions A} → (P ≡ Q → False) → Injection (pQQR {P = P} {Q} {R})
Injection.property (pQQRSubsetInj {P = P} {Q} {R} p!=q) {One} {One} refl = refl
Injection.property (pQQRSubsetInj {P = P} {Q} {R} p!=q) {One} {Two} pr with impliesInjective pr
Injection.property (pQQRSubsetInj {P = P} {Q} {R} p!=q) {One} {Two} pr | p=q ,, _ = exFalso (p!=q p=q)
Injection.property (pQQRSubsetInj {P = P} {Q} {R} p!=q) {Two} {One} pr with impliesInjective pr
Injection.property (pQQRSubsetInj {P = P} {Q} {R} p!=q) {Two} {One} pr | q=p ,, _ = exFalso (p!=q (equalityCommutative q=p))
Injection.property (pQQRSubsetInj {P = P} {Q} {R} p!=q) {Two} {Two} refl = refl

syntacticEntailmentExample : {a : _} {A : Set a} {P Q R : Propositions A} → (p!=q : P ≡ Q → False) → Proof propositionalAxioms (record { ofElt = pQQR {P = P} {Q} {R} }) 7
syntacticEntailmentExample {P = P} {Q} {R} p!=q = nextStep 6 (nextStep 5 (nextStep 4 (nextStep 3 (nextStep 2 (nextStep 1 (nextStep 0 empty (axiom (Two , record { one = P ; two = Q ; three = R }))) (given Two)) (axiom (One , ((implies Q R) ,, P)))) (modusPonens (record { element = implies (implies Q R) (implies P (implies Q R)) ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) (record { element = implies Q R ; position = 1 ; elementIsAt = refl ; pos<N = succPreservesInequality (succIsPositive _) }) (implies P (implies Q R)) refl)) (modusPonens (record { element = implies (implies P (implies Q R)) (implies (implies P Q) (implies P R)) ; position = 3 ; pos<N = le 0 refl ; elementIsAt = refl }) (record { element = implies P (implies Q R) ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) (implies (implies P Q) (implies P R)) refl)) (given One)) (modusPonens (record { element = implies (implies P Q) (implies P R) ; position = 1 ; pos<N = succPreservesInequality (succIsPositive _) ; elementIsAt = refl }) (record { element = implies P Q ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) (implies P R) refl)

pQQRProof : {a : _} {A : Set a} {P Q R : Propositions A} → (p!=q : P ≡ Q → False) → Proves propositionalAxioms (record { ofElt = pQQR {P = P} {Q} {R} }) (implies P R)
pQQRProof p!=q = record { n = 6 ; proof = syntacticEntailmentExample p!=q ; ofStatement = refl }

-- Subset {p}
pSubset : {a : _} {A : Set a} {P : Propositions A} → True → Propositions A
pSubset {P = P} record {} = implies P P

pSubsetInj : {a : _} {A : Set a} {P : Propositions A} → Injection (pSubset {P = P})
Injection.property (pSubsetInj {P = P}) {record {}} {record {}} refl = refl

syntacticEntailmentPP : {a : _} {A : Set a} {P : Propositions A} → Proof propositionalAxioms record { ofElt = pSubset {P = P} } 5
syntacticEntailmentPP {P = P} = nextStep 4 (nextStep 3 (nextStep 2 (nextStep 1 (nextStep 0 empty (axiom (One , (P ,, (implies P P))))) (axiom (Two , record { one = P ; two = implies P P ; three = P }))) (modusPonens (record { element = implies (implies P (implies (implies P P) P)) (implies (implies P (implies P P)) (implies P P)) ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) (record { element = implies P (implies (implies P P) P) ; position = 1 ; pos<N = succPreservesInequality (succIsPositive _) ; elementIsAt = refl }) (implies (implies P (implies P P)) (implies P P)) refl)) (axiom (One , (P ,, P)))) (modusPonens (record { element = implies (implies P (implies P P)) (implies P P) ; position = 1 ; pos<N = succPreservesInequality (succIsPositive _) ; elementIsAt = refl }) (record { element = implies P (implies P P) ; position = 0 ; pos<N = succIsPositive _ ; elementIsAt = refl }) (implies P P) refl)

pImpliesP : {a : _} {A : Set a} {P : Propositions A} → Proves propositionalAxioms record { ofElt = pSubset {P = P} } (implies P P)
Proves.n (pImpliesP {P = P}) = 4
Proves.proof (pImpliesP {P = P}) = syntacticEntailmentPP {P = P}
Proves.ofStatement (pImpliesP {P = P}) = refl
