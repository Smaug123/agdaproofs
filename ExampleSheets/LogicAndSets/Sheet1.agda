{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Logic.PropositionalLogic

module ExampleSheets.LogicAndSets.Sheet1 where

  q1i : {a : _} {A : Set a} → (p1 p2 p3 : Propositions A) → Tautology (implies (implies p1 (implies p2 p3)) (implies p2 (implies p1 p3)))
  Tautology.isTaut (q1i p1 p2 p3) {v} with inspect (Valuation.v v p3)
  Tautology.isTaut (q1i p1 p2 p3) {v} | BoolTrue with≡ p3T = Valuation.vImplicationT v (Valuation.vImplicationT v (Valuation.vImplicationT v p3T))
  Tautology.isTaut (q1i p1 p2 p3) {v} | BoolFalse with≡ p3F with inspect (Valuation.v v p2)
  Tautology.isTaut (q1i p1 p2 p3) {v} | BoolFalse with≡ p3F | BoolTrue with≡ p2T with inspect (Valuation.v v p1)
  Tautology.isTaut (q1i p1 p2 p3) {v} | BoolFalse with≡ p3F | BoolTrue with≡ p2T | BoolTrue with≡ p1T = Valuation.vImplicationVacuous v (Valuation.vImplicationF v p1T (Valuation.vImplicationF v p2T p3F))
  Tautology.isTaut (q1i p1 p2 p3) {v} | BoolFalse with≡ p3F | BoolTrue with≡ p2T | BoolFalse with≡ p1F = Valuation.vImplicationT v (Valuation.vImplicationT v (Valuation.vImplicationVacuous v p1F))
  Tautology.isTaut (q1i p1 p2 p3) {v} | BoolFalse with≡ p3F | BoolFalse with≡ p2F = Valuation.vImplicationT v (Valuation.vImplicationVacuous v p2F)
