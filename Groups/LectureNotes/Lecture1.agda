{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Integers.Integers
open import Numbers.Rationals.Definition
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Sets.Cardinality.Finite.Definition
open import Groups.Definition
open import Groups.Groups
open import Groups.Abelian.Definition
open import Groups.FiniteGroups.Definition
open import Rings.Definition
open import Numbers.Modulo.Group
open import Numbers.Modulo.Definition
open import Semirings.Definition

module Groups.LectureNotes.Lecture1 where

ℤIsGroup : _
ℤIsGroup = ℤGroup

ℚIsGroup : _
ℚIsGroup = Ring.additiveGroup ℚRing

-- TODO: R is a group with +

integersMinusNotGroup : Group (reflSetoid ℤ) (_-Z_) → False
integersMinusNotGroup record { +WellDefined = wellDefined ; 0G = identity ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with multAssoc {nonneg 3} {nonneg 2} {nonneg 1}
integersMinusNotGroup record { +WellDefined = wellDefined ; 0G = identity ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | ()

negSuccInjective : {a b : ℕ} → (negSucc a ≡ negSucc b) → a ≡ b
negSuccInjective {a} {.a} refl = refl

nonnegInjective : {a b : ℕ} → (nonneg a ≡ nonneg b) → a ≡ b
nonnegInjective {a} {.a} refl = refl

integersTimesNotGroup : Group (reflSetoid ℤ) (_*Z_) → False
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (nonneg zero) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with multIdentLeft {negSucc 1}
... | ()
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (nonneg (succ zero)) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with invLeft {nonneg zero}
... | bl with inverse (nonneg zero)
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (nonneg (succ zero)) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | () | nonneg zero
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (nonneg (succ zero)) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | p | nonneg (succ x) = naughtE (nonnegInjective (transitivity (applyEquality nonneg (equalityCommutative (Semiring.productZeroRight ℕSemiring x))) p))
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (nonneg (succ zero)) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | () | negSucc x
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (nonneg (succ (succ x))) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with succInjective (negSuccInjective (multIdentLeft {negSucc 1}))
... | ()
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (negSucc x) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with multIdentLeft {nonneg 2}
integersTimesNotGroup record { +WellDefined = wellDefined ; 0G = (negSucc x) ; inverse = inverse ; +Associative = multAssoc ; identRight = multIdentRight ; identLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | ()

-- TODO: Q is not a group with *Q
-- TODO: Q without 0 is a group with *Q
-- TODO: {1, -1} is a group with *

ℤnIsGroup : (n : ℕ) → (0<n : 0 <N n) → _
ℤnIsGroup n pr = ℤnGroup n pr

-- Groups example 8.9 from lecture 1
data Weird : Set where
  e : Weird
  a : Weird
  b : Weird
  c : Weird

_+W_ : Weird → Weird → Weird
e +W t = t
a +W e = a
a +W a = e
a +W b = c
a +W c = b
b +W e = b
b +W a = c
b +W b = e
b +W c = a
c +W e = c
c +W a = b
c +W b = a
c +W c = e

+WAssoc : {x y z : Weird} → (x +W (y +W z)) ≡ (x +W y) +W z
+WAssoc {e} {y} {z} = refl
+WAssoc {a} {e} {z} = refl
+WAssoc {a} {a} {e} = refl
+WAssoc {a} {a} {a} = refl
+WAssoc {a} {a} {b} = refl
+WAssoc {a} {a} {c} = refl
+WAssoc {a} {b} {e} = refl
+WAssoc {a} {b} {a} = refl
+WAssoc {a} {b} {b} = refl
+WAssoc {a} {b} {c} = refl
+WAssoc {a} {c} {e} = refl
+WAssoc {a} {c} {a} = refl
+WAssoc {a} {c} {b} = refl
+WAssoc {a} {c} {c} = refl
+WAssoc {b} {e} {z} = refl
+WAssoc {b} {a} {e} = refl
+WAssoc {b} {a} {a} = refl
+WAssoc {b} {a} {b} = refl
+WAssoc {b} {a} {c} = refl
+WAssoc {b} {b} {e} = refl
+WAssoc {b} {b} {a} = refl
+WAssoc {b} {b} {b} = refl
+WAssoc {b} {b} {c} = refl
+WAssoc {b} {c} {e} = refl
+WAssoc {b} {c} {a} = refl
+WAssoc {b} {c} {b} = refl
+WAssoc {b} {c} {c} = refl
+WAssoc {c} {e} {z} = refl
+WAssoc {c} {a} {e} = refl
+WAssoc {c} {a} {a} = refl
+WAssoc {c} {a} {b} = refl
+WAssoc {c} {a} {c} = refl
+WAssoc {c} {b} {e} = refl
+WAssoc {c} {b} {a} = refl
+WAssoc {c} {b} {b} = refl
+WAssoc {c} {b} {c} = refl
+WAssoc {c} {c} {e} = refl
+WAssoc {c} {c} {a} = refl
+WAssoc {c} {c} {b} = refl
+WAssoc {c} {c} {c} = refl

weirdGroup : Group (reflSetoid Weird) _+W_
Group.+WellDefined weirdGroup = reflGroupWellDefined
Group.0G weirdGroup = e
Group.inverse weirdGroup t = t
Group.+Associative weirdGroup {r} {s} {t} = +WAssoc {r} {s} {t}
Group.identRight weirdGroup {e} = refl
Group.identRight weirdGroup {a} = refl
Group.identRight weirdGroup {b} = refl
Group.identRight weirdGroup {c} = refl
Group.identLeft weirdGroup {e} = refl
Group.identLeft weirdGroup {a} = refl
Group.identLeft weirdGroup {b} = refl
Group.identLeft weirdGroup {c} = refl
Group.invLeft weirdGroup {e} = refl
Group.invLeft weirdGroup {a} = refl
Group.invLeft weirdGroup {b} = refl
Group.invLeft weirdGroup {c} = refl
Group.invRight weirdGroup {e} = refl
Group.invRight weirdGroup {a} = refl
Group.invRight weirdGroup {b} = refl
Group.invRight weirdGroup {c} = refl

weirdAb : AbelianGroup weirdGroup
AbelianGroup.commutative weirdAb {e} {e} = refl
AbelianGroup.commutative weirdAb {e} {a} = refl
AbelianGroup.commutative weirdAb {e} {b} = refl
AbelianGroup.commutative weirdAb {e} {c} = refl
AbelianGroup.commutative weirdAb {a} {e} = refl
AbelianGroup.commutative weirdAb {a} {a} = refl
AbelianGroup.commutative weirdAb {a} {b} = refl
AbelianGroup.commutative weirdAb {a} {c} = refl
AbelianGroup.commutative weirdAb {b} {e} = refl
AbelianGroup.commutative weirdAb {b} {a} = refl
AbelianGroup.commutative weirdAb {b} {b} = refl
AbelianGroup.commutative weirdAb {b} {c} = refl
AbelianGroup.commutative weirdAb {c} {e} = refl
AbelianGroup.commutative weirdAb {c} {a} = refl
AbelianGroup.commutative weirdAb {c} {b} = refl
AbelianGroup.commutative weirdAb {c} {c} = refl

weirdProjection : Weird → FinSet 4
weirdProjection a = ofNat 0 (le 3 refl)
weirdProjection b = ofNat 1 (le 2 refl)
weirdProjection c = ofNat 2 (le 1 refl)
weirdProjection e = ofNat 3 (le zero refl)

weirdProjectionSurj : Surjection weirdProjection
weirdProjectionSurj fzero = a , refl
weirdProjectionSurj (fsucc fzero) = b , refl
weirdProjectionSurj (fsucc (fsucc fzero)) = c , refl
weirdProjectionSurj (fsucc (fsucc (fsucc fzero))) = e , refl
weirdProjectionSurj (fsucc (fsucc (fsucc (fsucc ()))))

weirdProjectionInj : (x y : Weird) → weirdProjection x ≡ weirdProjection y → Setoid._∼_ (reflSetoid Weird) x y
weirdProjectionInj e e fx=fy = refl
weirdProjectionInj e a ()
weirdProjectionInj e b ()
weirdProjectionInj e c ()
weirdProjectionInj a e ()
weirdProjectionInj a a fx=fy = refl
weirdProjectionInj a b ()
weirdProjectionInj a c ()
weirdProjectionInj b e ()
weirdProjectionInj b a ()
weirdProjectionInj b b fx=fy = refl
weirdProjectionInj b c ()
weirdProjectionInj c e ()
weirdProjectionInj c a ()
weirdProjectionInj c b ()
weirdProjectionInj c c fx=fy = refl

weirdFinite : FiniteGroup weirdGroup (FinSet 4)
SetoidToSet.project (FiniteGroup.toSet weirdFinite) = weirdProjection
SetoidToSet.wellDefined (FiniteGroup.toSet weirdFinite) x y = applyEquality weirdProjection
SetoidToSet.surj (FiniteGroup.toSet weirdFinite) = weirdProjectionSurj
SetoidToSet.inj (FiniteGroup.toSet weirdFinite) = weirdProjectionInj
FiniteSet.size (FiniteGroup.finite weirdFinite) = 4
FiniteSet.mapping (FiniteGroup.finite weirdFinite) = id
FiniteSet.bij (FiniteGroup.finite weirdFinite) = idIsBijective

weirdOrder : groupOrder weirdFinite ≡ 4
weirdOrder = refl

-- TODO: dihedral groups
-- TODO: matrix groups on R
-- TODO: general linear groups on R
