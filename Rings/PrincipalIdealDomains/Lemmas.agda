{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Rings.Definition
open import Rings.PrincipalIdealDomains.Definition
open import Rings.IntegralDomains.Definition
open import Rings.Ideals.Maximal.Definition
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.PrincipalIdealDomains.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) (pid : {c : _} → PrincipalIdealDomain intDom {c}) where

open import Rings.Ideals.Definition R
open import Rings.Irreducibles.Definition intDom
open import Rings.Ideals.Principal.Definition R
open import Rings.Divisible.Definition R
open import Rings.Associates.Lemmas intDom
open import Rings.Ideals.Lemmas R
open import Rings.Units.Definition R
open import Rings.Irreducibles.Lemmas intDom
open import Rings.Units.Lemmas R

open Ring R
open Setoid S
open Equivalence eq

irreducibleImpliesMaximalIdeal : (r : A) → Irreducible r → {d : _} → MaximalIdeal (generatedIdeal r) {d}
MaximalIdeal.notContained (irreducibleImpliesMaximalIdeal r irred {d}) = 1R
MaximalIdeal.notContainedIsNotContained (irreducibleImpliesMaximalIdeal r irred {d}) = Irreducible.nonunit irred
MaximalIdeal.isMaximal (irreducibleImpliesMaximalIdeal r irred {d}) {biggerPred} bigger biggerContains (outsideR , (biggerContainsOutside ,, notInR)) {x} = biggerPrincipal' (unitImpliesGeneratedIdealEverything w {x})
  where
    biggerGen : A
    biggerGen = PrincipalIdeal.generator (pid bigger)
    biggerPrincipal : {x : A} → biggerPred x → biggerGen ∣ x
    biggerPrincipal = PrincipalIdeal.genGenerates (pid bigger)
    bp : biggerPred biggerGen
    bp = PrincipalIdeal.genIsInIdeal (pid bigger)
    biggerPrincipal' : {x : A} → biggerGen ∣ x → biggerPred x
    biggerPrincipal' {y} bg|y = memberDividesImpliesMember bigger bp bg|y
    u : biggerGen ∣ r
    u = biggerPrincipal (biggerContains (1R , transitive *Commutative identIsIdent))
    biggerGenNonzero : biggerGen ∼ 0R → False
    biggerGenNonzero bg=0 = notInR (Ideal.isSubset (generatedIdeal r) (symmetric t) (Ideal.containsIdentity (generatedIdeal r)))
      where
        t : outsideR ∼ 0R
        t with biggerPrincipal {outsideR} biggerContainsOutside
        ... | mult , pr = transitive (symmetric pr) (transitive (*WellDefined bg=0 reflexive) (transitive *Commutative timesZero))
    v : (r ∣ biggerGen) → False
    v r|bg with mutualDivisionImpliesAssociate r|bg u (Irreducible.nonzero irred)
    v r|bg | assoc = notInR (associateImpliesGeneratedIdealsEqual' assoc (PrincipalIdeal.genGenerates (pid bigger) biggerContainsOutside))
    w : Unit biggerGen
    w = dividesIrreducibleImpliesUnit irred u v
