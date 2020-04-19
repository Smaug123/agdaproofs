{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Cosets
open import Groups.Homomorphisms.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Setoids
open import Setoids.Functions.Lemmas
open import Rings.Definition
open import Sets.EquivalenceRelations
open import Rings.Ideals.Definition
open import Fields.Fields
open import Fields.Lemmas
open import Rings.Cosets
open import Rings.Ideals.Maximal.Definition
open import Rings.Ideals.Lemmas
open import Rings.Ideals.Prime.Definition
open import Rings.IntegralDomains.Definition
open import Rings.Ideals.Prime.Lemmas

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Maximal.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} {c : _} {pred : A → Set c} (i : Ideal R pred)  where


open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq

idealMaximalImpliesQuotientField : ({d : Level} → MaximalIdeal i {d}) → Field (cosetRing R i)
Field.allInvertible (idealMaximalImpliesQuotientField max) cosetA cosetA!=0 = ans' , ans''
  where
    gen : Ideal (cosetRing R i) (generatedIdealPred (cosetRing R i) cosetA)
    gen = generatedIdeal (cosetRing R i) cosetA
    inv : Ideal R (inverseImagePred {S = S} {T = cosetSetoid additiveGroup (Ideal.isSubgroup i)} (GroupHom.wellDefined (RingHom.groupHom (cosetRingHom R i))) (Ideal.isSubset gen))
    inv = inverseImageIsIdeal (cosetRing R i) (cosetRingHom R i) gen
    containsOnce : {a : A} → (Ideal.predicate i a) → (Ideal.predicate inv a)
    containsOnce {x} ix = x , ((x , Ideal.closedUnderPlus i (Ideal.closedUnderInverse i ix) (Ideal.isSubset i *Commutative (Ideal.accumulatesTimes i ix))) ,, Ideal.isSubset i (symmetric invLeft) (Ideal.containsIdentity i))
    notInI : A
    notInI = cosetA
    notInIIsInInv : Ideal.predicate inv notInI
    notInIIsInInv = cosetA , ((1R , Ideal.isSubset i {0R} (symmetric (transitive (+WellDefined reflexive (transitive *Commutative identIsIdent)) (invLeft {cosetA}))) (Ideal.containsIdentity i)) ,, Ideal.isSubset i (symmetric invLeft) (Ideal.containsIdentity i))
    notInIPr : (Ideal.predicate i notInI) → False
    notInIPr iInI = cosetA!=0 (Ideal.isSubset i (transitive (symmetric identLeft) (+WellDefined (symmetric (invIdent additiveGroup)) reflexive)) iInI)
    ans : {a : A} → Ideal.predicate inv a
    ans = MaximalIdeal.isMaximal max inv containsOnce (notInI , (notInIIsInInv ,, notInIPr))
    ans' : A
    ans' with ans {1R}
    ... | _ , ((b , _) ,, _) = b
    ans'' : pred (inverse (Ring.1R (cosetRing R i)) + (ans' * cosetA))
    ans'' with ans {1R}
    ans'' | a , ((b , predCAb-a) ,, pred1-a) = Ideal.isSubset i (transitive (+WellDefined (invContravariant additiveGroup) reflexive) (transitive +Associative (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) *Commutative))) (Ideal.closedUnderPlus i (Ideal.closedUnderInverse i pred1-a) predCAb-a)
Field.nontrivial (idealMaximalImpliesQuotientField max) 1=0 = MaximalIdeal.notContainedIsNotContained max (Ideal.isSubset i (identIsIdent {MaximalIdeal.notContained (max {lzero})}) (Ideal.accumulatesTimes i p))
  where
    have : pred (inverse 1R)
    have = Ideal.isSubset i identRight 1=0
    p : pred 1R
    p = Ideal.isSubset i (invTwice additiveGroup 1R) (Ideal.closedUnderInverse i have)

quotientFieldImpliesIdealMaximal : Field (cosetRing R i) → ({d : _} → MaximalIdeal i {d})
MaximalIdeal.notContained (quotientFieldImpliesIdealMaximal f) = Ring.1R (cosetRing R i)
MaximalIdeal.notContainedIsNotContained (quotientFieldImpliesIdealMaximal f) p1R = Field.nontrivial f (memberDividesImpliesMember R i p1R ((inverse 1R + 0R) , identIsIdent))
MaximalIdeal.isMaximal (quotientFieldImpliesIdealMaximal f) {bigger} biggerIdeal contained (a , (biggerA ,, notPredA)) = Ideal.isSubset biggerIdeal identIsIdent (Ideal.accumulatesTimes biggerIdeal v)
  where
    inv : Sg A (λ t → pred (inverse 1R + (t * a)))
    inv = Field.allInvertible f a λ r → notPredA (translate' R i r)
    r : A
    r = underlying inv
    s : pred (inverse 1R + (r * a))
    s with inv
    ... | _ , p = p
    t : bigger (inverse 1R + (r * a))
    t = contained s
    u : bigger (inverse (r * a))
    u = Ideal.closedUnderInverse biggerIdeal (Ideal.isSubset biggerIdeal *Commutative (Ideal.accumulatesTimes biggerIdeal biggerA))
    v : bigger 1R
    v = Ideal.isSubset biggerIdeal (invTwice additiveGroup 1R) (Ideal.closedUnderInverse biggerIdeal (Ideal.isSubset biggerIdeal (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) (Ideal.closedUnderPlus biggerIdeal t u)))

idealMaximalImpliesIdealPrime : ({d : _} → MaximalIdeal i {d}) → PrimeIdeal i
idealMaximalImpliesIdealPrime max = quotientIntDomImpliesIdealPrime i (fieldIsIntDom (idealMaximalImpliesQuotientField max))

maximalIdealWellDefined : {d : _} {pred2 : A → Set d} (i2 : Ideal R pred2) → ({x : A} → pred x → pred2 x) → ({x : A} → pred2 x → pred x) → {e : _} → MaximalIdeal i {e} → MaximalIdeal i2 {e}
MaximalIdeal.notContained (maximalIdealWellDefined i2 pToP2 p2ToP record { notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained ; isMaximal = isMaximal }) = notContained
MaximalIdeal.notContainedIsNotContained (maximalIdealWellDefined i2 pToP2 p2ToP record { notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained ; isMaximal = isMaximal }) p2Not = notContainedIsNotContained (p2ToP p2Not)
MaximalIdeal.isMaximal (maximalIdealWellDefined i2 pToP2 p2ToP record { notContained = notContained ; notContainedIsNotContained = notContainedIsNotContained ; isMaximal = isMaximal }) {biggerPred} bigger pred2InBigger (r , (biggerPredR ,, notP2r)) {x} = isMaximal bigger (λ p → pred2InBigger (pToP2 p)) (r , (biggerPredR ,, λ p → notP2r (pToP2 p)))
