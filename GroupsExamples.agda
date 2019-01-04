{-# OPTIONS --safe --warning=error #-}

open import Groups
open import Orders
open import Integers
open import Setoids
open import LogicalFormulae
open import FinSet
open import Functions
open import Naturals
open import IntegersModN
open import RingExamples
open import PrimeNumbers
open import Groups2

module GroupsExamples where
  integersMinusNotGroup : Group (reflSetoid ℤ) (_-Z_) → False
  integersMinusNotGroup record { wellDefined = wellDefined ; identity = identity ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with multAssoc {nonneg 3} {nonneg 2} {nonneg 1}
  integersMinusNotGroup record { wellDefined = wellDefined ; identity = identity ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | ()

  integersTimesNotGroup : Group (reflSetoid ℤ) (_*Z_) → False
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (nonneg zero) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with multIdentLeft {negSucc 1}
  ... | ()
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (nonneg (succ zero)) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with invLeft {nonneg zero}
  ... | bl with inverse (nonneg zero)
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (nonneg (succ zero)) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | () | nonneg zero
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (nonneg (succ zero)) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | () | nonneg (succ x)
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (nonneg (succ zero)) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | () | negSucc x
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (nonneg (succ (succ x))) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with succInjective (negSuccInjective (multIdentLeft {negSucc 1}))
  ... | ()
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (negSucc x) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } with multIdentLeft {nonneg 2}
  integersTimesNotGroup record { wellDefined = wellDefined ; identity = (negSucc x) ; inverse = inverse ; multAssoc = multAssoc ; multIdentRight = multIdentRight ; multIdentLeft = multIdentLeft ; invLeft = invLeft ; invRight = invRight } | ()

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
  Group.wellDefined weirdGroup = reflGroupWellDefined
  Group.identity weirdGroup = e
  Group.inverse weirdGroup t = t
  Group.multAssoc weirdGroup {r} {s} {t} = +WAssoc {r} {s} {t}
  Group.multIdentRight weirdGroup {e} = refl
  Group.multIdentRight weirdGroup {a} = refl
  Group.multIdentRight weirdGroup {b} = refl
  Group.multIdentRight weirdGroup {c} = refl
  Group.multIdentLeft weirdGroup {e} = refl
  Group.multIdentLeft weirdGroup {a} = refl
  Group.multIdentLeft weirdGroup {b} = refl
  Group.multIdentLeft weirdGroup {c} = refl
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
  Surjection.property weirdProjectionSurj fzero = a , refl
  Surjection.property weirdProjectionSurj (fsucc fzero) = b , refl
  Surjection.property weirdProjectionSurj (fsucc (fsucc fzero)) = c , refl
  Surjection.property weirdProjectionSurj (fsucc (fsucc (fsucc fzero))) = e , refl
  Surjection.property weirdProjectionSurj (fsucc (fsucc (fsucc (fsucc ()))))

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

  elementPowZ : (n : ℕ) → (elementPower ℤGroup (nonneg 1) n) ≡ nonneg n
  elementPowZ zero = refl
  elementPowZ (succ n) rewrite elementPowZ n = refl

  ℤCyclic : CyclicGroup ℤGroup
  CyclicGroup.generator ℤCyclic = nonneg 1
  CyclicGroup.cyclic ℤCyclic {nonneg x} = inl (x , elementPowZ x)
  CyclicGroup.cyclic ℤCyclic {negSucc x} = inr (succ x , ans)
    where
      ans : additiveInverseZ (nonneg 1 +Z elementPower ℤGroup (nonneg 1) x) ≡ negSucc x
      ans rewrite elementPowZ x = refl

  elementPowZn : (n : ℕ) → {pr : 0 <N succ (succ n)} → (power : ℕ) → (powerLess : power <N succ (succ n)) → {p : 1 <N succ (succ n)} → elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) power ≡ record { x = power ; xLess = powerLess }
  elementPowZn n zero powerLess = equalityZn _ _ refl
  elementPowZn n {pr} (succ power) powerLess {p} with orderIsTotal (ℤn.x (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) power)) (succ n)
  elementPowZn n {pr} (succ power) powerLess {p} | inl (inl x) = equalityZn _ _ (applyEquality succ v)
    where
      t : elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = succPreservesInequality (succIsPositive n) }) power ≡ record { x = power ; xLess = PartialOrder.transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess }
      t = elementPowZn n {pr} power (PartialOrder.transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess) {succPreservesInequality (succIsPositive n)}
      u : elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) power ≡ record { x = power ; xLess = PartialOrder.transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess }
      u rewrite <NRefl p (succPreservesInequality (succIsPositive n)) = t
      v : ℤn.x (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) power) ≡ power
      v rewrite u = refl
  elementPowZn n {pr} (succ power) powerLess {p} | inl (inr x) with elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) power
  elementPowZn n {pr} (succ power) powerLess {p} | inl (inr x) | record { x = x' ; xLess = xLess } = exFalso (noIntegersBetweenXAndSuccX _ x xLess)
  elementPowZn n {pr} (succ power) powerLess {p} | inr x with inspect (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) power)
  elementPowZn n {pr} (succ power) powerLess {p} | inr x | record { x = x' ; xLess = p' } with≡ inspected rewrite elementPowZn n {pr} power (PartialOrder.transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess) {p} | x = exFalso (PartialOrder.irreflexive (TotalOrder.order ℕTotalOrder) powerLess)

  ℤnCyclic : (n : ℕ) → (pr : 0 <N n) → CyclicGroup (ℤnGroup n pr)
  ℤnCyclic zero ()
  CyclicGroup.generator (ℤnCyclic (succ zero) pr) = record { x = 0 ; xLess = pr }
  CyclicGroup.cyclic (ℤnCyclic (succ zero) pr) {record { x = zero ; xLess = xLess }} rewrite <NRefl xLess (succIsPositive 0) | <NRefl pr (succIsPositive 0) = inl (0 , refl)
  CyclicGroup.cyclic (ℤnCyclic (succ zero) _) {record { x = succ x ; xLess = xLess }} = exFalso (zeroNeverGreater (canRemoveSuccFrom<N xLess))
  ℤnCyclic (succ (succ n)) pr = record { generator = record { x = 1 ; xLess = succPreservesInequality (succIsPositive n) } ; cyclic = λ {x} → inl (ans x) }
    where
      ans : (z : ℤn (succ (succ n)) pr) → Sg ℕ (λ i → (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = succPreservesInequality (succIsPositive n) }) i) ≡ z)
      ans record { x = x ; xLess = xLess } = x , elementPowZn n x xLess

  multiplyByNHom : (n : ℕ) → GroupHom ℤGroup ℤGroup (λ i → i *Z nonneg n)
  GroupHom.groupHom (multiplyByNHom n) {x} {y} = lemma1
    where
      open Setoid (reflSetoid ℤ)
      open Group ℤGroup
      lemma : nonneg n *Z (x +Z y) ≡ (nonneg n) *Z x +Z nonneg n *Z y
      lemma = additionZDistributiveMulZ (nonneg n) x y
      lemma1 : (x +Z y) *Z nonneg n ≡ x *Z nonneg n +Z y *Z nonneg n
      lemma1 rewrite multiplicationZIsCommutative (x +Z y) (nonneg n) | multiplicationZIsCommutative x (nonneg n) | multiplicationZIsCommutative y (nonneg n) = lemma
  GroupHom.wellDefined (multiplyByNHom n) {x} {.x} refl = refl

  modNExampleGroupHom : (n : ℕ) → (pr : 0 <N n) → GroupHom ℤGroup (ℤnGroup n pr) (mod n pr)
  modNExampleGroupHom = {!!}

  intoZn : {n : ℕ} → {pr : 0 <N n} → (x : ℕ) → (x<n : x <N n) → mod n pr (nonneg x) ≡ record { x = x ; xLess = x<n }
  intoZn {zero} {()}
  intoZn {succ n} {0<n} x x<n with divisionAlg (succ n) x
  intoZn {succ n} {0<n} x x<n | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl y ; quotSmall = quotSmall } = equalityZn _ _ (modIsUnique (record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl y ; quotSmall = quotSmall }) (record { quot = 0 ; rem = x ; pr = ans ; remIsSmall = inl x<n ; quotSmall = inl (succIsPositive n)}))
    where
      ans : n *N 0 +N x ≡ x
      ans rewrite multiplicationNIsCommutative n 0 = refl
  intoZn {succ n} {0<n} x x<n | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }

  quotientZn : (n : ℕ) → (pr : 0 <N n) → GroupIso (quotientGroup ℤGroup (modNExampleGroupHom n pr)) (ℤnGroup n pr) (mod n pr)
  GroupHom.groupHom (GroupIso.groupHom (quotientZn n pr)) = GroupHom.groupHom (modNExampleGroupHom n pr)
  GroupHom.wellDefined (GroupIso.groupHom (quotientZn n pr)) {x} {y} x~y = need
    where
      given : mod n pr (x +Z (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr }
      given = x~y
      given' : (mod n pr x) +n (mod n pr (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr }
      given' = transitivity (equalityCommutative (GroupHom.groupHom (modNExampleGroupHom n pr))) given
      given'' : (mod n pr x) +n Group.inverse (ℤnGroup n pr) (mod n pr y) ≡ record { x = 0 ; xLess = pr}
      given'' = transitivity (applyEquality (λ i → mod n pr x +n i) (equalityCommutative (homRespectsInverse (modNExampleGroupHom n pr)))) given'
      need : mod n pr x ≡ mod n pr y
      need = transferToRight (ℤnGroup n pr) given''
  GroupIso.inj (quotientZn n pr) {x} {y} fx~fy = need
    where
      given : mod n pr x +n Group.inverse (ℤnGroup n pr) (mod n pr y) ≡ record { x = 0 ; xLess = pr }
      given = transferToRight'' (ℤnGroup n pr) fx~fy
      given' : mod n pr (x +Z (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr }
      given' = identityOfIndiscernablesLeft _ _ _ _≡_ given (equalityCommutative (transitivity (GroupHom.groupHom (modNExampleGroupHom n pr) {x}) (applyEquality (λ i → mod n pr x +n i) (homRespectsInverse (modNExampleGroupHom n pr)))))
      need' : (mod n pr x) +n (mod n pr (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr }
      need' rewrite equalityCommutative (GroupHom.groupHom (modNExampleGroupHom n pr) {x} {Group.inverse ℤGroup y}) = given'
      need : mod n pr (x +Z (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr}
      need = identityOfIndiscernablesLeft _ _ _ _≡_ need' (equalityCommutative (GroupHom.groupHom (modNExampleGroupHom n pr)))
  GroupIso.surj (quotientZn n pr) {record { x = x ; xLess = xLess }} = nonneg x , intoZn x xLess

  trivialGroupHom : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) → GroupHom trivialGroup G (λ _ → Group.identity G)
  GroupHom.groupHom (trivialGroupHom {S = S} G) = symmetric multIdentRight
    where
      open Setoid S
      open Group G
      open Symmetric (Equivalence.symmetricEq eq)
  GroupHom.wellDefined (trivialGroupHom {S = S} G) _ = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))

  trivialSubgroupIsNormal : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ : A → A → A} (G : Group S _+A_) → NormalSubgroup G trivialGroup (trivialGroupHom G)
  Subgroup.fInj (NormalSubgroup.subgroup (trivialSubgroupIsNormal G)) {fzero} {fzero} _ = refl
  Subgroup.fInj (NormalSubgroup.subgroup (trivialSubgroupIsNormal G)) {fzero} {fsucc ()} _
  Subgroup.fInj (NormalSubgroup.subgroup (trivialSubgroupIsNormal G)) {fsucc ()} {y} _
  NormalSubgroup.normal (trivialSubgroupIsNormal {S = S} {_+A_ = _+A_} G) = fzero , transitive (wellDefined (multIdentRight) reflexive) invRight
    where
      open Setoid S
      open Group G
      open Transitive (Equivalence.transitiveEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)

  improperSubgroupIsNormal : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ : A → A → A} (G : Group S _+A_) → NormalSubgroup G G (identityHom G)
  Subgroup.fInj (NormalSubgroup.subgroup (improperSubgroupIsNormal G)) = id
  NormalSubgroup.normal (improperSubgroupIsNormal {S = S} {_+A_ = _+A_} G) {g} {h} =  ((g +A h) +A inverse g) , reflexive
    where
      open Group G
      open Setoid S
      open Reflexive (Equivalence.reflexiveEq eq)
