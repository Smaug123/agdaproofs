{-# OPTIONS --safe --warning=error --with-K #-}

open import Sets.EquivalenceRelations
open import Groups.Definition
open import Orders
open import Rings.Definition
open import Numbers.Integers.Integers
open import Numbers.Integers.Multiplication
open import Setoids.Setoids
open import LogicalFormulae
open import Sets.FinSet
open import Functions
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.WithK
open import Numbers.Modulo.Definition
open import Numbers.Modulo.Addition
open import Numbers.Modulo.Group
open import Rings.Examples.Examples
open import Numbers.Primes.PrimeNumbers
open import Groups.Lemmas
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Isomorphisms.Definition
open import Groups.Cyclic.Definition
open import Groups.QuotientGroup.Definition
open import Groups.Subgroups.Definition
open import Groups.Subgroups.Normal.Definition

module Groups.Examples.Examples where

trivialGroup : Group (reflSetoid (FinSet 1)) λ _ _ → fzero
Group.+WellDefined trivialGroup _ _ = refl
Group.0G trivialGroup = fzero
Group.inverse trivialGroup _ = fzero
Group.+Associative trivialGroup = refl
Group.identRight trivialGroup {fzero} = refl
Group.identRight trivialGroup {fsucc ()}
Group.identLeft trivialGroup {fzero} = refl
Group.identLeft trivialGroup {fsucc ()}
Group.invLeft trivialGroup = refl
Group.invRight trivialGroup = refl

elementPowZ : (n : ℕ) → (elementPower ℤGroup (nonneg 1) (nonneg n)) ≡ nonneg n
elementPowZ zero = refl
elementPowZ (succ n) rewrite elementPowZ n = refl

ℤCyclic : CyclicGroup ℤGroup
CyclicGroup.generator ℤCyclic = nonneg 1
CyclicGroup.cyclic ℤCyclic {nonneg x} = (nonneg x , elementPowZ x)
CyclicGroup.cyclic ℤCyclic {negSucc x} = (negSucc x , ans)
  where
    ans : (Group.inverse ℤGroup ((nonneg 1) +Z elementPower ℤGroup (nonneg 1) (nonneg x))) ≡ negSucc x
    ans rewrite elementPowZ x = refl

elementPowZn : (n : ℕ) → {pr : 0 <N succ (succ n)} → (power : ℕ) → (powerLess : power <N succ (succ n)) → {p : 1 <N succ (succ n)} → elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) (nonneg power) ≡ record { x = power ; xLess = powerLess }
elementPowZn n zero powerLess = equalityZn _ _ refl
elementPowZn n {pr} (succ power) powerLess {p} with TotalOrder.totality ℕTotalOrder (ℤn.x (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) (nonneg power))) (succ n)
elementPowZn n {pr} (succ power) powerLess {p} | inl (inl x) = equalityZn _ _ (applyEquality succ v)
  where
    t : elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = succPreservesInequality (succIsPositive n) }) (nonneg power) ≡ record { x = power ; xLess = PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess }
    t = elementPowZn n {pr} power (PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess) {succPreservesInequality (succIsPositive n)}
    u : elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) (nonneg power) ≡ record { x = power ; xLess = PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess }
    u rewrite <NRefl p (succPreservesInequality (succIsPositive n)) = t
    v : ℤn.x (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) (nonneg power)) ≡ power
    v rewrite u = refl
elementPowZn n {pr} (succ power) powerLess {p} | inl (inr x) with elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) (nonneg power)
elementPowZn n {pr} (succ power) powerLess {p} | inl (inr x) | record { x = x' ; xLess = xLess } = exFalso (noIntegersBetweenXAndSuccX _ x xLess)
elementPowZn n {pr} (succ power) powerLess {p} | inr x with inspect (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = p }) (nonneg power))
elementPowZn n {pr} (succ power) powerLess {p} | inr x | record { x = x' ; xLess = p' } with≡ inspected rewrite elementPowZn n {pr} power (PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) (a<SuccA power) powerLess) {p} | x = exFalso (PartialOrder.irreflexive (TotalOrder.order ℕTotalOrder) powerLess)

ℤnCyclic : (n : ℕ) → (pr : 0 <N n) → CyclicGroup (ℤnGroup n pr)
ℤnCyclic zero ()
CyclicGroup.generator (ℤnCyclic (succ zero) pr) = record { x = 0 ; xLess = pr }
CyclicGroup.cyclic (ℤnCyclic (succ zero) pr) {record { x = zero ; xLess = xLess }} rewrite <NRefl xLess (succIsPositive 0) | <NRefl pr (succIsPositive 0) = (nonneg 0 , refl)
CyclicGroup.cyclic (ℤnCyclic (succ zero) _) {record { x = succ x ; xLess = xLess }} = exFalso (zeroNeverGreater (canRemoveSuccFrom<N xLess))
ℤnCyclic (succ (succ n)) pr = record { generator = record { x = 1 ; xLess = succPreservesInequality (succIsPositive n) } ; cyclic = λ {x} → ans x }
  where
    ans : (z : ℤn (succ (succ n)) pr) → Sg ℤ (λ i → (elementPower (ℤnGroup (succ (succ n)) pr) (record { x = 1 ; xLess = succPreservesInequality (succIsPositive n) }) i) ≡ z)
    ans record { x = x ; xLess = xLess } = nonneg x , elementPowZn n x xLess

multiplyByNHom : (n : ℕ) → GroupHom ℤGroup ℤGroup (λ i → i *Z nonneg n)
GroupHom.groupHom (multiplyByNHom n) {x} {y} = lemma1
  where
    open Setoid (reflSetoid ℤ)
    open Group ℤGroup
    lemma : nonneg n *Z (x +Z y) ≡ (nonneg n) *Z x +Z nonneg n *Z y
    lemma = Ring.*DistributesOver+ ℤRing {nonneg n} {x} {y}
    lemma1 : (x +Z y) *Z nonneg n ≡ x *Z nonneg n +Z y *Z nonneg n
    lemma1 rewrite Ring.*Commutative ℤRing {x +Z y} {nonneg n} | Ring.*Commutative ℤRing {x} {nonneg n} | Ring.*Commutative ℤRing {y} {nonneg n} = lemma
GroupHom.wellDefined (multiplyByNHom n) {x} {.x} refl = refl

modNExampleGroupHom : (n : ℕ) → (pr : 0 <N n) → GroupHom ℤGroup (ℤnGroup n pr) (mod n pr)
GroupHom.groupHom (modNExampleGroupHom n 0<n) {x} {y} = {!!}
GroupHom.wellDefined (modNExampleGroupHom n 0<n) {x} {.x} refl = refl

intoZn : {n : ℕ} → {pr : 0 <N n} → (x : ℕ) → (x<n : x <N n) → mod n pr (nonneg x) ≡ record { x = x ; xLess = x<n }
intoZn {zero} {()}
intoZn {succ n} {0<n} x x<n with divisionAlg (succ n) x
intoZn {succ n} {0<n} x x<n | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl y ; quotSmall = quotSmall } = equalityZn _ _ (modIsUnique (record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl y ; quotSmall = quotSmall }) (record { quot = 0 ; rem = x ; pr = ans ; remIsSmall = inl x<n ; quotSmall = inl (succIsPositive n)}))
  where
    ans : n *N 0 +N x ≡ x
    ans rewrite multiplicationNIsCommutative n 0 = refl
intoZn {succ n} {0<n} x x<n | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }

quotientZn : (n : ℕ) → (pr : 0 <N n) → GroupIso (quotientGroupByHom ℤGroup (modNExampleGroupHom n pr)) (ℤnGroup n pr) (mod n pr)
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
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (quotientZn n pr))) {x} {y} x=y = {!!}
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (quotientZn n pr))) {x} {y} = SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (quotientZn n pr))) {x} {y}
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (quotientZn n pr))) {x} {y} fx~fy = need
  where
    given : mod n pr x +n Group.inverse (ℤnGroup n pr) (mod n pr y) ≡ record { x = 0 ; xLess = pr }
    given = transferToRight'' (ℤnGroup n pr) fx~fy
    given' : mod n pr (x +Z (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr }
    given' = identityOfIndiscernablesLeft _≡_ given (equalityCommutative (transitivity (GroupHom.groupHom (modNExampleGroupHom n pr) {x}) (applyEquality (λ i → mod n pr x +n i) (homRespectsInverse (modNExampleGroupHom n pr)))))
    need' : (mod n pr x) +n (mod n pr (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr }
    need' rewrite equalityCommutative (GroupHom.groupHom (modNExampleGroupHom n pr) {x} {Group.inverse ℤGroup y}) = given'
    need : mod n pr (x +Z (Group.inverse ℤGroup y)) ≡ record { x = 0 ; xLess = pr}
    need = identityOfIndiscernablesLeft _≡_ need' (equalityCommutative (GroupHom.groupHom (modNExampleGroupHom n pr)))
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (quotientZn n pr))) {record { x = x ; xLess = xLess }} = nonneg x , intoZn x xLess

trivialGroupHom : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) → GroupHom trivialGroup G (λ _ → Group.0G G)
GroupHom.groupHom (trivialGroupHom {S = S} G) = symmetric identRight
  where
    open Setoid S
    open Group G
    open Equivalence eq
GroupHom.wellDefined (trivialGroupHom {S = S} G) _ = Equivalence.reflexive (Setoid.eq S)
