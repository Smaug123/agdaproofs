{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Integers
open import Groups.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Isomorphisms.Definition
open import Groups.Abelian.Definition
open import Groups.Subgroups.Definition
open import Groups.Lemmas
open import Groups.Groups
open import Rings.Definition
open import Rings.Lemmas
open import Fields.Fields
open import Sets.EquivalenceRelations

module Groups.Examples.ExampleSheet1 where

  {-
    Question 1: e is the unique solution of x^2 = x
  -}
  question1 : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} → (G : Group S _+_) → (x : A) → Setoid._∼_ S (x + x) x → Setoid._∼_ S x (Group.0G G)
  question1 {S = S} {_+_ = _+_} G x x+x=x = transitive (symmetric identRight) (transitive (+WellDefined reflexive (symmetric invRight)) (transitive +Associative (transitive (+WellDefined x+x=x reflexive) invRight)))
    where
      open Group G
      open Setoid S
      open Equivalence eq

  question1' : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} → (G : Group S _+_) → Setoid._∼_ S ((Group.0G G) + (Group.0G G)) (Group.0G G)
  question1' G = Group.identRight G

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
      open Equivalence eq
      bad : Setoid._∼_ S xCoeff2 0R
      bad with Field.allInvertible F xCoeff1 xCoeffNonzero1
      ... | xinv , pr' = transitive (symmetric identIsIdent) (transitive (*WellDefined (symmetric pr') reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive pr) (Ring.timesZero R))))
  LinearFunction.constant (composeLinearFunctions {_+_ = _+_} {_*_ = _*_} record { xCoeff = xCoeff1 ; xCoeffNonzero = xCoeffNonzero1 ; constant = constant1 } record { xCoeff = xCoeff2 ; xCoeffNonzero = xCoeffNonzero2 ; constant = constant2 }) = (xCoeff1 * constant2) + constant1

  compositionIsCorrect : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} (f1 : LinearFunction F) (f2 : LinearFunction F) → {r : A} → Setoid._∼_ S (interpretLinearFunction (composeLinearFunctions f1 f2) r) (((interpretLinearFunction f1) ∘ (interpretLinearFunction f2)) r)
  compositionIsCorrect {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant } record { xCoeff = xCoeff' ; xCoeffNonzero = xCoeffNonzero' ; constant = constant' } {r} = ans
    where
      open Setoid S
      open Ring R
      open Equivalence eq
      ans : (((xCoeff * xCoeff') * r) + ((xCoeff * constant') + constant)) ∼ (xCoeff * ((xCoeff' * r) + constant')) + constant
      ans = transitive (Group.+Associative additiveGroup) (Group.+WellDefined additiveGroup (transitive (Group.+WellDefined additiveGroup (symmetric (Ring.*Associative R)) reflexive) (symmetric (Ring.*DistributesOver+ R))) (reflexive {constant}))

  linearFunctionsSetoid : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : Field R) → Setoid (LinearFunction I)
  Setoid._∼_ (linearFunctionsSetoid {S = S} I) f1 f2 = ((LinearFunction.xCoeff f1) ∼ (LinearFunction.xCoeff f2)) && ((LinearFunction.constant f1) ∼ (LinearFunction.constant f2))
    where
      open Setoid S
  Equivalence.reflexive (Setoid.eq (linearFunctionsSetoid {S = S} I)) = Equivalence.reflexive (Setoid.eq S) ,, Equivalence.reflexive (Setoid.eq S)
  Equivalence.symmetric (Setoid.eq (linearFunctionsSetoid {S = S} I)) (fst ,, snd) = Equivalence.symmetric (Setoid.eq S) fst ,, Equivalence.symmetric (Setoid.eq S) snd
  Equivalence.transitive (Setoid.eq (linearFunctionsSetoid {S = S} I)) (fst1 ,, snd1) (fst2 ,, snd2) = Equivalence.transitive (Setoid.eq S) fst1 fst2 ,, Equivalence.transitive (Setoid.eq S) snd1 snd2

  linearFunctionsGroup : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) → Group (linearFunctionsSetoid F) (composeLinearFunctions)
  Group.+WellDefined (linearFunctionsGroup {R = R} F) {record { xCoeff = xCoeffM ; xCoeffNonzero = xCoeffNonzeroM ; constant = constantM }} {record { xCoeff = xCoeffN ; xCoeffNonzero = xCoeffNonzeroN ; constant = constantN }} {record { xCoeff = xCoeffX ; xCoeffNonzero = xCoeffNonzeroX ; constant = constantX }} {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} (fst1 ,, snd1) (fst2 ,, snd2) = *WellDefined fst1 fst2 ,, Group.+WellDefined additiveGroup (*WellDefined fst1 snd2) snd1
    where
      open Ring R
  Group.0G (linearFunctionsGroup {S = S} {R = R} F) = record { xCoeff = Ring.1R R ; constant = Ring.0R R ; xCoeffNonzero = λ p → Field.nontrivial F (Equivalence.symmetric (Setoid.eq S) p) }
  Group.inverse (linearFunctionsGroup {S = S} {_*_ = _*_} {R = R} F) record { xCoeff = xCoeff ; constant = c ; xCoeffNonzero = pr } with Field.allInvertible F xCoeff pr
  ... | (inv , pr') = record { xCoeff = inv ; constant = inv * (Group.inverse (Ring.additiveGroup R) c) ; xCoeffNonzero = λ p → Field.nontrivial F (transitive (symmetric (transitive (Ring.*WellDefined R p reflexive) (transitive (Ring.*Commutative R) (Ring.timesZero R)))) pr') }
    where
      open Setoid S
      open Equivalence eq
  Group.+Associative (linearFunctionsGroup {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} F) {record { xCoeff = xA ; xCoeffNonzero = xANonzero ; constant = cA }} {record { xCoeff = xB ; xCoeffNonzero = xBNonzero ; constant = cB }} {record { xCoeff = xC ; xCoeffNonzero = xCNonzero ; constant = cC }} = Ring.*Associative R ,, transitive (Group.+WellDefined additiveGroup (transitive *DistributesOver+ (Group.+WellDefined additiveGroup *Associative reflexive)) reflexive) (symmetric (Group.+Associative additiveGroup))
    where
      open Setoid S
      open Equivalence eq
      open Ring R
  Group.identRight (linearFunctionsGroup {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} = transitive (Ring.*Commutative R) (Ring.identIsIdent R) ,, transitive (Group.+WellDefined additiveGroup (Ring.timesZero R) reflexive) (Group.identLeft additiveGroup)
    where
      open Ring R
      open Setoid S
      open Equivalence eq
  Group.identLeft (linearFunctionsGroup {S = S} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} = identIsIdent ,, transitive (Group.identRight additiveGroup) identIsIdent
    where
      open Setoid S
      open Ring R
      open Equivalence eq
  Group.invLeft (linearFunctionsGroup F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} with Field.allInvertible F xCoeff xCoeffNonzero
  Group.invLeft (linearFunctionsGroup {S = S} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} | inv , prInv = prInv ,, transitive (symmetric *DistributesOver+) (transitive (*WellDefined reflexive (Group.invRight additiveGroup)) (Ring.timesZero R))
    where
      open Setoid S
      open Ring R
      open Equivalence eq
  Group.invRight (linearFunctionsGroup {S = S} {R = R} F) {record { xCoeff = xCoeff ; xCoeffNonzero = xCoeffNonzero ; constant = constant }} with Field.allInvertible F xCoeff xCoeffNonzero
  ... | inv , pr = transitive *Commutative pr  ,, transitive (Group.+WellDefined additiveGroup *Associative reflexive) (transitive (Group.+WellDefined additiveGroup (*WellDefined (transitive *Commutative pr) reflexive) reflexive) (transitive (Group.+WellDefined additiveGroup identIsIdent reflexive) (Group.invLeft additiveGroup)))
    where
      open Setoid S
      open Ring R
      open Equivalence eq

  {-
    Question 3, part 2: prove that linearFunctionsGroup is not abelian
  -}

  -- We'll assume the field doesn't have characteristic 2.
  linearFunctionsGroupNotAbelian : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {F : Field R} → (nonChar2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) → AbelianGroup (linearFunctionsGroup F) → False
  linearFunctionsGroupNotAbelian {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {F = F} pr record { commutative = commutative } = ans
    where
      open Ring R
      open Group additiveGroup
      open Equivalence (Setoid.eq S) renaming (symmetric to symmetricS ; transitive to transitiveS ; reflexive to reflexiveS)

      f : LinearFunction F
      f = record { xCoeff = 1R ; xCoeffNonzero = λ p → Field.nontrivial F (symmetricS p) ; constant = 1R }
      g : LinearFunction F
      g = record { xCoeff = 1R + 1R ; xCoeffNonzero = pr ; constant = 0R }

      gf : LinearFunction F
      gf = record { xCoeff = 1R + 1R ; xCoeffNonzero = pr ; constant = 1R + 1R }

      fg : LinearFunction F
      fg = record { xCoeff = 1R + 1R ; xCoeffNonzero = pr ; constant = 1R }

      oneWay : Setoid._∼_ (linearFunctionsSetoid F) gf (composeLinearFunctions g f)
      oneWay = symmetricS (transitiveS *Commutative identIsIdent) ,, transitiveS (symmetricS (transitiveS *Commutative identIsIdent)) (symmetricS (Group.identRight additiveGroup))

      otherWay : Setoid._∼_ (linearFunctionsSetoid F) fg (composeLinearFunctions f g)
      otherWay = symmetricS identIsIdent ,, transitiveS (symmetricS (Group.identLeft additiveGroup)) (Group.+WellDefined additiveGroup (symmetricS identIsIdent) (reflexiveS {1R}))

      open Equivalence (Setoid.eq (linearFunctionsSetoid F))
      bad : Setoid._∼_ (linearFunctionsSetoid F) gf fg
      bad = transitive {gf} {composeLinearFunctions g f} {fg} oneWay (transitive {composeLinearFunctions g f} {composeLinearFunctions f g} {fg} (commutative {g} {f}) (symmetric {fg} {composeLinearFunctions f g} otherWay))

      ans : False
      ans with bad
      ans | _ ,, contr = Field.nontrivial F (symmetricS (transitiveS {1R} {1R + (1R + Group.inverse additiveGroup 1R)} (transitiveS (symmetricS (Group.identRight additiveGroup)) (Group.+WellDefined additiveGroup reflexiveS (symmetricS (Group.invRight additiveGroup)))) (transitiveS (Group.+Associative additiveGroup) (transitiveS (Group.+WellDefined additiveGroup contr reflexiveS) (Group.invRight additiveGroup)))))
