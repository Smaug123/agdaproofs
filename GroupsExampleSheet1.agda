{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Naturals
open import Integers
open import FinSet
open import Groups
open import Rings
open import Fields

module GroupsExampleSheet1 where

  {-
    Question 1: e is the unique solution of x^2 = x
  -}
  question1 : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} → (G : Group S _+_) → (x : A) → Setoid._∼_ S (x + x) x → Setoid._∼_ S x (Group.identity G)
  question1 {S = S} {_+_ = _+_} G x x+x=x = transitive (symmetric multIdentRight) (transitive (wellDefined reflexive (symmetric invRight)) (transitive multAssoc (transitive (wellDefined x+x=x reflexive) invRight)))
    where
      open Group G
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  question1' : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} → (G : Group S _+_) → Setoid._∼_ S ((Group.identity G) + (Group.identity G)) (Group.identity G)
  question1' G = Group.multIdentRight G

  {-
    Question 2: intersection of subgroups is a subgroup; union of subgroups is a subgroup iff one is contained in the other.

    First, define the intersection of subgroups and show that it is a subgroup.
  -}
  data SubgroupIntersectionElement {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) : Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f) where
    ofElt : {x : A} → Sg B (λ b → Setoid._∼_ S (h1Inj b) x) → Sg C (λ c → Setoid._∼_ S (h2Inj c) x) → SubgroupIntersectionElement G H1 H2

  subgroupIntersectionOp : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) → (r : SubgroupIntersectionElement G H1 H2) → (s : SubgroupIntersectionElement G H1 H2) → SubgroupIntersectionElement G H1 H2
  subgroupIntersectionOp {S = S} {_+_ = _+_} {_+H1_ = _+H1_} {_+H2_ = _+H2_} G {h1Hom = h1Hom} {h2Hom = h2Hom} H1 H2 (ofElt (b , prB) (c , prC)) (ofElt (b2 , prB2) (c2 , prC2)) = ofElt ((b +H1 b2) , GroupHom.groupHom h1Hom) ((c +H2 c2) , transitive (GroupHom.groupHom h2Hom) (transitive (Group.wellDefined G prC prC2) (Group.wellDefined G (symmetric prB) (symmetric prB2))))
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  subgroupIntersectionSetoid : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) → Setoid (SubgroupIntersectionElement G H1 H2)
  Setoid._∼_ (subgroupIntersectionSetoid {T = T} {U = U} G {h1Inj = h1} {h2Inj = h2} H1 H2) (ofElt (xH1 , prxH1) (xH2 , prxH2)) (ofElt (yH1 , pryH1) (yH2 , pryH2)) = (Setoid._∼_ T xH1 yH1) && (Setoid._∼_ U xH2 yH2)
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (subgroupIntersectionSetoid {T = T} {U = U} G H1 H2))) {ofElt (a , prA) (b , prB)} = (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T))) ,, (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq U)))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (subgroupIntersectionSetoid {T = T} {U = U} G H1 H2))) {ofElt (a , prA) (b , prB)} {ofElt (c , prC) (d , prD)} (fst ,, snd) = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq T)) fst ,, Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq U)) snd
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (subgroupIntersectionSetoid {T = T} {U = U} G H1 H2))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst1 ,, snd1) (fst2 ,, snd2) = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq T)) fst1 fst2 ,, Transitive.transitive (Equivalence.transitiveEq (Setoid.eq U)) snd1 snd2

  subgroupIntersectionGroup : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) → Group (subgroupIntersectionSetoid G H1 H2) (subgroupIntersectionOp G H1 H2)
  Group.wellDefined (subgroupIntersectionGroup {S = S} {T = T} {U = U} G {H1grp = h1} {H2grp = h2} H1 H2) {ofElt (_ , _) (_ , _)} {ofElt (_ , _ ) (_ , _)} {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (pr1 ,, pr2) (pr3 ,, pr4) = transitiveT (Group.wellDefined h1 pr1 reflexiveT) (Group.wellDefined h1 reflexiveT pr3) ,, transitiveU (Group.wellDefined h2 pr2 reflexiveU) ((Group.wellDefined h2 reflexiveU pr4))
    where
      open Group G
      open Setoid T
      open Transitive (Equivalence.transitiveEq (Setoid.eq T)) renaming (transitive to transitiveT)
      open Symmetric (Equivalence.symmetricEq (Setoid.eq T)) renaming (symmetric to symmetricT)
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq T)) renaming (reflexive to reflexiveT)
      open Transitive (Equivalence.transitiveEq (Setoid.eq U)) renaming (transitive to transitiveU)
      open Symmetric (Equivalence.symmetricEq (Setoid.eq U)) renaming (symmetric to symmetricU)
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq U)) renaming (reflexive to reflexiveU)
  Group.identity (subgroupIntersectionGroup G {H1grp = H1grp} {H2grp = H2grp} {h1Hom = h1Hom} {h2Hom = h2Hom} H1 H2) = ofElt {x = Group.identity G} (Group.identity H1grp , imageOfIdentityIsIdentity h1Hom) (Group.identity H2grp , imageOfIdentityIsIdentity h2Hom)
  Group.inverse (subgroupIntersectionGroup {S = S} G {H1grp = h1} {H2grp = h2} {h1Hom = h1hom} {h2Hom = h2hom} H1 H2) (ofElt (a , prA) (b , prB)) = ofElt (Group.inverse h1 a , homRespectsInverse h1hom) (Group.inverse h2 b , transitive (homRespectsInverse h2hom) (inverseWellDefined G (transitive prB (symmetric prA))))
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Group.multAssoc (subgroupIntersectionGroup G {H1grp = h1} {H2grp = h2} H1 H2) {ofElt (a , prA) (b , prB)} {ofElt (c , prC) (d , prD)} {ofElt (e , prE) (f , prF)} = Group.multAssoc h1 ,, Group.multAssoc h2
  Group.multIdentRight (subgroupIntersectionGroup G {H1grp = h1} {H2grp = h2} H1 H2) {ofElt (_ , _) (_ , _)} = Group.multIdentRight h1 ,, Group.multIdentRight h2
  Group.multIdentLeft (subgroupIntersectionGroup G {H1grp = h1} {H2grp = h2} H1 H2) {ofElt (_ , _) (_ , _)} = Group.multIdentLeft h1 ,, Group.multIdentLeft h2
  Group.invLeft (subgroupIntersectionGroup G {H1grp = h1} {H2grp = h2} H1 H2) {ofElt (_ , _) (_ , _)} = Group.invLeft h1 ,, Group.invLeft h2
  Group.invRight (subgroupIntersectionGroup G {H1grp = h1} {H2grp = h2} H1 H2) {ofElt (_ , _) (_ , _)} = Group.invRight h1 ,, Group.invRight h2

  subgroupIntersectionInjectionIntoMain : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) → SubgroupIntersectionElement G H1 H2 → A
  subgroupIntersectionInjectionIntoMain G {h1Inj = f} H1 H2 (ofElt (a , prA) (b , prB)) = f a

  subgroupIntersectionInjectionIntoMainIsHom : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) → GroupHom (subgroupIntersectionGroup G H1 H2) G (subgroupIntersectionInjectionIntoMain G H1 H2)
  GroupHom.groupHom (subgroupIntersectionInjectionIntoMainIsHom G {h1Hom = h1} H1 H2) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} = GroupHom.groupHom h1
  GroupHom.wellDefined (subgroupIntersectionInjectionIntoMainIsHom G {h1Hom = h1} H1 H2) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, snd) = GroupHom.wellDefined h1 fst

  subgroupIntersectionIsSubgroup : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) → Subgroup G (subgroupIntersectionGroup G H1 H2) (subgroupIntersectionInjectionIntoMainIsHom G H1 H2)
  SetoidInjection.wellDefined (Subgroup.fInj (subgroupIntersectionIsSubgroup G {h1Hom = h1} H1 H2)) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, snd) = GroupHom.wellDefined h1 fst
  SetoidInjection.injective (Subgroup.fInj (subgroupIntersectionIsSubgroup {S = S} G H1 H2)) {ofElt (a , prA) (b , prB)} {ofElt (c , prC) (d , prD)} x~y = SetoidInjection.injective (Subgroup.fInj H1) x~y ,, SetoidInjection.injective (Subgroup.fInj H2) (transitive prB (transitive (transitive (symmetric prA) (transitive x~y prC) ) (symmetric prD)))
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  {-
    To make sure we haven't defined something stupid, check that the intersection doesn't care which order the two subgroups came in, and check that the subgroup intersection is isomorphic to the original group in the case that the two were the same, and check that the intersection injects into the first subgroup.
  -}

  subgroupIntersectionIsomorphic : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {_+_ : A → A → A} {_+H1_ : B → B → B} {_+H2_ : C → C → C} (G : Group S _+_) {H1grp : Group T _+H1_} {H2grp : Group U _+H2_} {h1Inj : B → A} {h2Inj : C → A} {h1Hom : GroupHom H1grp G h1Inj} {h2Hom : GroupHom H2grp G h2Inj} (H1 : Subgroup G H1grp h1Hom) (H2 : Subgroup G H2grp h2Hom) → GroupsIsomorphic (subgroupIntersectionGroup G H1 H2) (subgroupIntersectionGroup G H2 H1)
  GroupsIsomorphic.isomorphism (subgroupIntersectionIsomorphic G H1 H2) (ofElt (a , prA) (b , prB)) = ofElt (b , prB) (a , prA)
  GroupHom.groupHom (GroupIso.groupHom (GroupsIsomorphic.proof (subgroupIntersectionIsomorphic {T = T} {U = U} G H1 H2))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq U)) ,, Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T))
  GroupHom.wellDefined (GroupIso.groupHom (GroupsIsomorphic.proof (subgroupIntersectionIsomorphic G H1 H2))) {ofElt (a , prA) (b , prB)} {ofElt (_ , _) (_ , _)} (fst ,, snd) = snd ,, fst
  SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionIsomorphic G H1 H2)))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, snd) = snd ,, fst
  SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionIsomorphic G H1 H2)))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, snd) = snd ,, fst
  SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionIsomorphic G H1 H2)))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, snd) = snd ,, fst
  SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionIsomorphic {T = T} {U = U} G H1 H2)))) {ofElt (a , prA) (b , prB)} = ofElt (b , prB) (a , prA) , (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq U)) ,, Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T)))

  subgroupIntersectionOfSame : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {_+H1_ : B → B → B} (G : Group S _+_) {H1grp : Group T _+H1_} {h1Inj : B → A} {h1Hom : GroupHom H1grp G h1Inj} (H1 : Subgroup G H1grp h1Hom) → GroupsIsomorphic (subgroupIntersectionGroup G H1 H1) H1grp
  GroupsIsomorphic.isomorphism (subgroupIntersectionOfSame G H1) (ofElt (a , prA) (b , prB)) = a
  GroupHom.groupHom (GroupIso.groupHom (GroupsIsomorphic.proof (subgroupIntersectionOfSame {T = T} G H1))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T))
  GroupHom.wellDefined (GroupIso.groupHom (GroupsIsomorphic.proof (subgroupIntersectionOfSame G H1))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, _) = fst
  SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionOfSame G H1)))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, _) = fst
  SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionOfSame {S = S} {T = T} G {h1Hom = h1Hom} H1)))) {ofElt (a , prA) (b , prB)} {ofElt (c , prC) (d , prD)} a~b = a~b ,, SetoidInjection.injective (Subgroup.fInj H1) (transitive prB (transitive (transitive (symmetric prA) (transitive (GroupHom.wellDefined h1Hom a~b) prC)) (symmetric prD)))
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionOfSame G H1)))) {ofElt (_ , _) (_ , _)} {ofElt (_ , _) (_ , _)} (fst ,, _) = fst
  SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (subgroupIntersectionOfSame {S = S} {T = T} G H1)))) {b} = ofElt (b , Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (b , Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) , (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T)))

  {- TODO: finish question 2 -}

  {-
    Question 3. We can't talk about ℝ yet, so we'll just work in an arbitrary integral domain.
    Show that the collection of linear functions over a ring forms a group; is it abelian?
  -}

  record LinearFunction {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) : Set (a ⊔ b) where
    field
      xCoeff : A
      xCoeffNonzero : (Setoid._∼_ S xCoeff (Ring.0R R) → False)
      constant : A

  interpretLinearFunction : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} (f : LinearFunction F) → A → A
  interpretLinearFunction {_+_ = _+_} {_*_ = _*_} record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant } a = (xCoeff * a) + constant

  composeLinearFunctions : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} (f1 : LinearFunction F) (f2 : LinearFunction F) → LinearFunction F
  LinearFunction.xCoeff (composeLinearFunctions {_+_ = _+_} {_*_ = _*_} record { xCoeff = xCoeff1 ; xCoeffNonzero = xCoeffNonzero1 ; constant = constant1 } record { xCoeff = xCoeff2 ; xCoeffNonzero = xCoeffNonzero2 ; constant = constant2 }) = xCoeff1 * xCoeff2
  LinearFunction.xCoeffNonzero (composeLinearFunctions {S = S} {R = R} {F = F} record { xCoeff = xCoeff1 ; xCoeffNonzero = xCoeffNonzero1 ; constant = constant1 } record { xCoeff = xCoeff2 ; xCoeffNonzero = xCoeffNonzero2 ; constant = constant2 }) pr = xCoeffNonzero2 bad
    where
      open Setoid S
      open Ring R
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      bad : Setoid._∼_ S xCoeff2 0R
      bad with Field.allInvertible F xCoeff1 xCoeffNonzero1
      ... | xinv , pr' = transitive (symmetric multIdentIsIdent) (transitive (multWellDefined (symmetric pr') reflexive) (transitive (symmetric multAssoc) (transitive (multWellDefined reflexive pr) (ringTimesZero R))))
  LinearFunction.constant (composeLinearFunctions {_+_ = _+_} {_*_ = _*_} record { xCoeff = xCoeff1 ; xCoeffNonzero = xCoeffNonzero1 ; constant = constant1 } record { xCoeff = xCoeff2 ; xCoeffNonzero = xCoeffNonzero2 ; constant = constant2 }) = (xCoeff1 * constant2) + constant1

  compositionIsCorrect : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} (f1 : LinearFunction F) (f2 : LinearFunction F) → {r : A} → Setoid._∼_ S (interpretLinearFunction (composeLinearFunctions f1 f2) r) (((interpretLinearFunction f1) ∘ (interpretLinearFunction f2)) r)
  compositionIsCorrect {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant } record { xCoeff = xCoeff' ; xCoeffNonzero = xCoeffNonzero' ; constant = constant' } {r} = ans
    where
      open Setoid S
      open Ring R
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      ans : (((xCoeff * xCoeff') * r) + ((xCoeff * constant') + constant)) ∼ (xCoeff * ((xCoeff' * r) + constant')) + constant
      ans = transitive (Group.multAssoc additiveGroup) (Group.wellDefined additiveGroup (transitive (Group.wellDefined additiveGroup (symmetric (Ring.multAssoc R)) reflexive) (symmetric (Ring.multDistributes R))) (reflexive {constant}))

  linearFunctionsSetoid : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : Field R) → Setoid (LinearFunction I)
  Setoid._∼_ (linearFunctionsSetoid {S = S} I) f1 f2 = ((LinearFunction.xCoeff f1) ∼ (LinearFunction.xCoeff f2)) && ((LinearFunction.constant f1) ∼ (LinearFunction.constant f2))
    where
      open Setoid S
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (linearFunctionsSetoid {S = S} I))) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)) ,, Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (linearFunctionsSetoid {S = S} I))) (fst ,, snd) = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) fst ,, Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) snd
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (linearFunctionsSetoid {S = S} I))) (fst1 ,, snd1) (fst2 ,, snd2) = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) fst1 fst2 ,, Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) snd1 snd2

  linearFunctionsGroup : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) → Group (linearFunctionsSetoid F) (composeLinearFunctions)
  Group.wellDefined (linearFunctionsGroup {R = R} F) {record { xCoeff = xCoeffM ; xCoeffNonzero = xCoeffNonzeroM ; constant = constantM }} {record { xCoeff = xCoeffN ; xCoeffNonzero = xCoeffNonzeroN ; constant = constantN }} {record { xCoeff = xCoeffX ; xCoeffNonzero = xCoeffNonzeroX ; constant = constantX }} {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} (fst1 ,, snd1) (fst2 ,, snd2) = multWellDefined fst1 fst2 ,, Group.wellDefined additiveGroup (multWellDefined fst1 snd2) snd1
    where
      open Ring R
  Group.identity (linearFunctionsGroup {S = S} {R = R} F) = record { xCoeff = Ring.1R R ; constant = Ring.0R R ; xCoeffNonzero = λ p → Field.nontrivial F (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) p) }
  Group.inverse (linearFunctionsGroup {S = S} {_*_ = _*_} {R = R} F) record { xCoeff = xCoeff ; constant = c ; xCoeffNonzero = pr } with Field.allInvertible F xCoeff pr
  ... | (inv , pr') = record { xCoeff = inv ; constant = inv * (Group.inverse (Ring.additiveGroup R) c) ; xCoeffNonzero = λ p → Field.nontrivial F (transitive (symmetric (transitive (Ring.multWellDefined R p reflexive) (transitive (Ring.multCommutative R) (ringTimesZero R)))) pr') }
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Group.multAssoc (linearFunctionsGroup {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} F) {record { xCoeff = xA ; xCoeffNonzero = xANonzero ; constant = cA }} {record { xCoeff = xB ; xCoeffNonzero = xBNonzero ; constant = cB }} {record { xCoeff = xC ; xCoeffNonzero = xCNonzero ; constant = cC }} = Ring.multAssoc R ,, transitive (Group.wellDefined additiveGroup (transitive multDistributes (Group.wellDefined additiveGroup multAssoc reflexive)) reflexive) (symmetric (Group.multAssoc additiveGroup))
    where
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Setoid S
      open Ring R
  Group.multIdentRight (linearFunctionsGroup {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} = transitive (Ring.multCommutative R) (Ring.multIdentIsIdent R) ,, transitive (Group.wellDefined additiveGroup (ringTimesZero R) reflexive) (Group.multIdentLeft additiveGroup)
    where
      open Ring R
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Group.multIdentLeft (linearFunctionsGroup {S = S} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} = multIdentIsIdent ,, transitive (Group.multIdentRight additiveGroup) multIdentIsIdent
    where
      open Setoid S
      open Ring R
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
  Group.invLeft (linearFunctionsGroup F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} with Field.allInvertible F xCoeff xCoeffNonzero
  Group.invLeft (linearFunctionsGroup {S = S} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} | inv , prInv = prInv ,, transitive (symmetric multDistributes) (transitive (multWellDefined reflexive (Group.invRight additiveGroup)) (ringTimesZero R))
    where
      open Setoid S
      open Ring R
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Group.invRight (linearFunctionsGroup {S = S} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} with Field.allInvertible F xCoeff xCoeffNonzero
  ... | inv , pr = transitive multCommutative pr  ,, transitive (Group.wellDefined additiveGroup multAssoc reflexive) (transitive (Group.wellDefined additiveGroup (multWellDefined (transitive multCommutative pr) reflexive) reflexive) (transitive (Group.wellDefined additiveGroup multIdentIsIdent reflexive) (Group.invLeft additiveGroup)))
    where
      open Setoid S
      open Ring R
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  {-
    Question 3, part 2: prove that linearFunctionsGroup is not abelian
  -}

  -- We'll assume the field doesn't have characteristic 2.
  linearFunctionsGroupNotAbelian : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} → (nonChar2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) → AbelianGroup (linearFunctionsGroup F) → False
  linearFunctionsGroupNotAbelian {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {F = F} pr record { commutative = commutative } = ans
    where
      open Ring R
      open Group additiveGroup
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S)) renaming (symmetric to symmetricS)
      open Transitive (Equivalence.transitiveEq (Setoid.eq S)) renaming (transitive to transitiveS)
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S)) renaming (reflexive to reflexiveS)

      f : LinearFunction F
      f = record { xCoeff = 1R ; xCoeffNonzero = λ p → Field.nontrivial F (symmetricS p) ; constant = 1R }
      g : LinearFunction F
      g = record { xCoeff = 1R + 1R ; xCoeffNonzero = pr ; constant = 0R }

      gf : LinearFunction F
      gf = record { xCoeff = 1R + 1R ; xCoeffNonzero = pr ; constant = 1R + 1R }

      fg : LinearFunction F
      fg = record { xCoeff = 1R + 1R ; xCoeffNonzero = pr ; constant = 1R }

      oneWay : Setoid._∼_ (linearFunctionsSetoid F) gf (composeLinearFunctions g f)
      oneWay = symmetricS (transitiveS multCommutative multIdentIsIdent) ,, transitiveS (symmetricS (transitiveS multCommutative multIdentIsIdent)) (symmetricS (Group.multIdentRight additiveGroup))

      otherWay : Setoid._∼_ (linearFunctionsSetoid F) fg (composeLinearFunctions f g)
      otherWay = symmetricS multIdentIsIdent ,, transitiveS (symmetricS (Group.multIdentLeft additiveGroup)) (Group.wellDefined additiveGroup (symmetricS multIdentIsIdent) (reflexiveS {1R}))

      open Transitive (Equivalence.transitiveEq (Setoid.eq (linearFunctionsSetoid F)))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq (linearFunctionsSetoid F)))
      bad : Setoid._∼_ (linearFunctionsSetoid F) gf fg
      bad = transitive {gf} {composeLinearFunctions g f} {fg} oneWay (transitive {composeLinearFunctions g f} {composeLinearFunctions f g} {fg} (commutative {g} {f}) (symmetric {fg} {composeLinearFunctions f g} otherWay))

      ans : False
      ans with bad
      ans | _ ,, contr = Field.nontrivial F (symmetricS (transitiveS {1R} {1R + (1R + Group.inverse additiveGroup 1R)} (transitiveS (symmetricS (Group.multIdentRight additiveGroup)) (Group.wellDefined additiveGroup reflexiveS (symmetricS (Group.invRight additiveGroup)))) (transitiveS (Group.multAssoc additiveGroup) (transitiveS (Group.wellDefined additiveGroup contr reflexiveS) (Group.invRight additiveGroup)))))
