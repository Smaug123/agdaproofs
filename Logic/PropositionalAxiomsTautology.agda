{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Logic.PropositionalLogic
open import Functions.Definition
open import Numbers.Naturals.Naturals
open import Vectors
open import Boolean.Definition

module Logic.PropositionalAxiomsTautology where

axiomKTaut : {a : _} {A : Set a} (P Q : Propositions A) → Tautology (implies P (implies Q P))
axiomKTaut P Q v with inspect (Valuation.v v P)
axiomKTaut P Q v | BoolTrue with≡ pT with inspect (Valuation.v v Q)
axiomKTaut P Q v | BoolTrue with≡ pT | BoolTrue with≡ qT = Valuation.vImplicationT v (Valuation.vImplicationT v pT)
axiomKTaut P Q v | BoolTrue with≡ pT | BoolFalse with≡ qF = Valuation.vImplicationT v (Valuation.vImplicationVacuous v qF)
axiomKTaut P Q v | BoolFalse with≡ pF = Valuation.vImplicationVacuous v pF

axiomSTaut : {a : _} {A : Set a} (P Q R : Propositions A) → Tautology (implies (implies P (implies Q R)) (implies (implies P Q) (implies P R)))
axiomSTaut P Q R v with inspect (Valuation.v v P)
axiomSTaut P Q R v | BoolTrue with≡ pT with inspect (Valuation.v v Q)
axiomSTaut P Q R v | BoolTrue with≡ pT | BoolTrue with≡ qT with inspect (Valuation.v v R)
axiomSTaut P Q R v | BoolTrue with≡ pT | BoolTrue with≡ qT | BoolTrue with≡ rT = Valuation.vImplicationT v (Valuation.vImplicationT v (Valuation.vImplicationT v rT))
axiomSTaut P Q R v | BoolTrue with≡ pT | BoolTrue with≡ qT | BoolFalse with≡ rF = Valuation.vImplicationVacuous v (Valuation.vImplicationF v pT (Valuation.vImplicationF v qT rF))
axiomSTaut P Q R v | BoolTrue with≡ pT | BoolFalse with≡ qF = Valuation.vImplicationT v (Valuation.vImplicationVacuous v (Valuation.vImplicationF v pT qF))
axiomSTaut P Q R v | BoolFalse with≡ pF = Valuation.vImplicationT v (Valuation.vImplicationT v (Valuation.vImplicationVacuous v pF))

excludedMiddleTaut : {a : _} {A : Set a} (P : Propositions A) → Tautology (implies (prNot (prNot P)) P)
excludedMiddleTaut P v with inspect (Valuation.v v P)
excludedMiddleTaut P v | BoolTrue with≡ pT = Valuation.vImplicationT v pT
excludedMiddleTaut P v | BoolFalse with≡ pF = Valuation.vImplicationVacuous v (Valuation.vImplicationF v (Valuation.vImplicationVacuous v pF) (Valuation.vFalse v))

propositionalAxiomsTautology : {a : _} {A : Set a} (x : Sg ThreeElements (indexAxiom A)) → Tautology (IsSubset.ofElt propositionalAxioms x)
propositionalAxiomsTautology (One , (fst ,, snd)) = axiomKTaut fst snd
propositionalAxiomsTautology (Two , record { one = one ; two = two ; three = three }) = axiomSTaut one two three
propositionalAxiomsTautology (Three , b) = excludedMiddleTaut b
