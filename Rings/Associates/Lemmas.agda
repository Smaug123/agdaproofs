{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.IntegralDomains.Definition


module Rings.Associates.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Divisible.Definition R
open import Rings.IntegralDomains.Lemmas intDom
open import Rings.Associates.Definition intDom
open import Rings.Ideals.Definition R
open Setoid S
open Ring R
open Equivalence eq

associatesEquiv : Equivalence Associates
Equivalence.reflexive associatesEquiv {x} = 1R , ((1R , identIsIdent) ,, symmetric (transitive *Commutative identIsIdent))
Equivalence.symmetric associatesEquiv {x} {y} (a , ((invA , prInv) ,, x=ya)) = invA , ((a , transitive *Commutative prInv) ,, transitive (symmetric identIsIdent) (transitive (*WellDefined (symmetric prInv) reflexive) (transitive *Commutative (transitive *Associative (*WellDefined (symmetric x=ya) reflexive)))))
Equivalence.transitive associatesEquiv {x} {y} {z} (a , ((invA , prInvA) ,, x=ya)) (b , ((invB , prInvB) ,, y=zb)) = (a * b) , (((invA * invB) , transitive *Associative (transitive (*WellDefined (transitive *Commutative *Associative) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined (transitive *Commutative prInvA) prInvB) identIsIdent)))) ,, transitive x=ya (transitive (*WellDefined y=zb reflexive) (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative))))

associateImpliesMutualDivision : {a b : A} → Associates a b → a ∣ b
associateImpliesMutualDivision {a} {b} (x , ((invX , prInvX) ,, a=bx)) = invX , transitive (transitive (*WellDefined a=bx reflexive) (transitive (transitive (symmetric *Associative) (*WellDefined reflexive prInvX)) *Commutative)) identIsIdent

mutualDivisionImpliesAssociate : {a b : A} → (a ∣ b) → (b ∣ a) → ((a ∼ 0R) → False) → Associates a b
mutualDivisionImpliesAssociate {a} {b} (r , ar=b) (s , bs=a) a!=0 = s , ((r , cancelIntDom {a = a} (transitive (transitive (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (*WellDefined ar=b reflexive))) bs=a) (transitive (symmetric identIsIdent) *Commutative)) a!=0) ,, symmetric bs=a)

mutualDivisionImpliesAssociate' : {a b : A} → (a ∣ b) → (b ∣ a) → (a ∼ 0R) → Associates a b
mutualDivisionImpliesAssociate' {a} {b} (r , ar=b) (s , bs=a) a=0 = 1R , ((1R , identIsIdent) ,, transitive a=0 (symmetric (transitive (*WellDefined b=0 reflexive) (transitive *Commutative timesZero))))
  where
    b=0 : b ∼ 0R
    b=0 = transitive (symmetric ar=b) (transitive (transitive *Commutative (*WellDefined reflexive a=0)) (timesZero {r}))

associateImpliesGeneratedIdealsEqual : {a b : A} → Associates a b → {x : A} → generatedIdealPred a x → generatedIdealPred b x
associateImpliesGeneratedIdealsEqual {a} {b} (r , ((s , rs=1) ,, a=br)) {x} (c , ac=x) = (r * c) , transitive *Associative (transitive (*WellDefined (symmetric a=br) reflexive) ac=x)

associateImpliesGeneratedIdealsEqual' : {a b : A} → Associates a b → {x : A} → generatedIdealPred b x → generatedIdealPred a x
associateImpliesGeneratedIdealsEqual' assoc = associateImpliesGeneratedIdealsEqual (Equivalence.symmetric associatesEquiv assoc)
