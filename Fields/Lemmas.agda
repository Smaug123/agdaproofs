{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Rings.Definition
open import Groups.Definition
open import Fields.Fields
open import Sets.EquivalenceRelations
open import LogicalFormulae
open import Rings.IntegralDomains.Definition
open import Rings.IntegralDomains.Lemmas
open import Setoids.Subset

module Fields.Lemmas {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) where

open Setoid S
open Field F
open Ring R
open Group additiveGroup
open Equivalence eq
open import Rings.Lemmas R

halve : (charNot2 : ((1R + 1R) ∼ 0R) → False) → (a : A) → Sg A (λ i → i + i ∼ a)
halve charNot2 a with allInvertible (1R + 1R) charNot2
... | 1/2 , pr1/2 = (a * 1/2) , transitive (+WellDefined *Commutative *Commutative) (transitive (symmetric (*DistributesOver+ {1/2} {a} {a})) (transitive (*WellDefined (reflexive) r) (transitive (*Associative) (transitive (*WellDefined pr1/2 (reflexive)) identIsIdent))))
  where
    r : a + a ∼ (1R + 1R) * a
    r = symmetric (transitive *Commutative (transitive *DistributesOver+ (+WellDefined (transitive *Commutative identIsIdent) (transitive *Commutative identIsIdent))))

abstract

  halfHalves : {x : A} (1/2 : A) (pr : 1/2 + 1/2 ∼ 1R) → (x + x) * 1/2 ∼ x
  halfHalves {x} 1/2 pr = transitive (transitive (transitive *Commutative (transitive (transitive *DistributesOver+ (transitive (+WellDefined *Commutative *Commutative) (symmetric *DistributesOver+))) *Commutative)) (*WellDefined pr (reflexive))) identIsIdent

fieldIsIntDom : IntegralDomain R
IntegralDomain.intDom fieldIsIntDom {a} {b} ab=0 a!=0 with Field.allInvertible F a a!=0
IntegralDomain.intDom fieldIsIntDom {a} {b} ab=0 a!=0 | 1/a , prA = transitive (symmetric identIsIdent) (transitive (*WellDefined (symmetric prA) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive ab=0) (Ring.timesZero R))))
IntegralDomain.nontrivial fieldIsIntDom 1=0 = Field.nontrivial F (symmetric 1=0)

allInvertibleWellDefined : {a b : A} {a!=0 : (a ∼ 0F) → False} {b!=0 : (b ∼ 0F) → False} → (a ∼ b) → underlying (allInvertible a a!=0) ∼ underlying (allInvertible b b!=0)
allInvertibleWellDefined {a} {b} {a!=0} {b!=0} a=b with allInvertible a a!=0
... | x , prX with allInvertible b b!=0
... | y , prY with transitive (transitive prX (symmetric prY)) (*WellDefined reflexive (symmetric a=b))
... | xa=ya = cancelIntDom fieldIsIntDom (transitive *Commutative (transitive xa=ya *Commutative)) a!=0

private
  mulNonzeros : Sg A (λ m → (Setoid._∼_ S m (Ring.0R R)) → False) → Sg A (λ m → (Setoid._∼_ S m (Ring.0R R)) → False) → Sg A (λ m → (Setoid._∼_ S m (Ring.0R R)) → False)
  mulNonzeros (a , a!=0) (b , b!=0) = (a * b) , λ ab=0 → b!=0 (IntegralDomain.intDom (fieldIsIntDom) ab=0 a!=0)

fieldMultiplicativeGroup : Group (subsetSetoid S {pred = λ m → ((Setoid._∼_ S m (Ring.0R R)) → False)}(λ {x} {y} x=y x!=0 → λ y=0 → x!=0 (Equivalence.transitive (Setoid.eq S) x=y y=0))) (mulNonzeros)
Group.+WellDefined (fieldMultiplicativeGroup) {x , prX} {y , prY} {z , prZ} {w , prW} = Ring.*WellDefined R
Group.0G (fieldMultiplicativeGroup) = Ring.1R R , λ 1=0 → Field.nontrivial F (Equivalence.symmetric (Setoid.eq S) 1=0)
Group.inverse (fieldMultiplicativeGroup) (x , pr) with Field.allInvertible F x pr
... | 1/x , pr1/x = 1/x , λ 1/x=0 → Field.nontrivial F (Equivalence.transitive (Setoid.eq S) (Equivalence.symmetric (Setoid.eq S) (Equivalence.transitive (Setoid.eq S) (Ring.*WellDefined R 1/x=0 (Equivalence.reflexive (Setoid.eq S))) (Ring.timesZero' R))) pr1/x)
Group.+Associative (fieldMultiplicativeGroup) {x , prX} {y , prY} {z , prZ} = Ring.*Associative R
Group.identRight (fieldMultiplicativeGroup) {x , prX} = Ring.identIsIdent' R
Group.identLeft (fieldMultiplicativeGroup) {x , prX} = Ring.identIsIdent R
Group.invLeft (fieldMultiplicativeGroup) {x , prX} with Field.allInvertible F x prX
... | 1/x , pr1/x = pr1/x
Group.invRight (fieldMultiplicativeGroup) {x , prX} with Field.allInvertible F x prX
... | 1/x , pr1/x = Equivalence.transitive (Setoid.eq S) (Ring.*Commutative R) pr1/x
