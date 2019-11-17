{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Abelian.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Definition
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Vectors
open import Lists.Lists
open import Maybe

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Polynomials.Group {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Groups.Polynomials.Definition G
open import Groups.Polynomials.Addition G public
open Setoid S
open Equivalence eq

inverse : NaivePoly → NaivePoly
inverse = map (Group.inverse G)

invLeft : {a : NaivePoly} → polysEqual ((inverse a) +P a) []
invLeft {[]} = record {}
invLeft {x :: a} = Group.invLeft G ,, invLeft {a}

invRight : {a : NaivePoly} → polysEqual (a +P (inverse a)) []
invRight {[]} = record {}
invRight {x :: a} = Group.invRight G ,, invRight {a}

assoc : {a b c : NaivePoly} → polysEqual (a +P (b +P c)) ((a +P b) +P c)
assoc {[]} {[]} {[]} = record {}
assoc {[]} {[]} {x :: c} = reflexive ,, ans
  where
    ans : polysEqual (map (λ z → z) (map (λ z → z) c)) (map (λ z → z) c)
    ans rewrite mapId c | mapId c = Equivalence.reflexive (Setoid.eq naivePolySetoid)
assoc {[]} {b :: bs} {[]} = reflexive ,, ans
  where
    ans : polysEqual (map (λ z → z) (map (λ z → z) bs)) (map (λ z → z) (map (λ z → z) bs))
    ans rewrite mapId bs | mapId bs = Equivalence.reflexive (Setoid.eq naivePolySetoid)
assoc {[]} {b :: bs} {c :: cs} = reflexive ,, ans
  where
    ans : polysEqual (map (λ z → z) (listZip _+_ (λ z → z) (λ z → z) bs cs)) (listZip _+_ (λ z → z) (λ z → z) (map (λ z → z) bs) cs)
    ans rewrite mapId bs | mapId (listZip _+_ id id bs cs) = Equivalence.reflexive (Setoid.eq naivePolySetoid)
assoc {a :: as} {[]} {[]} = reflexive ,, ans
  where
    ans : polysEqual (map (λ z → z) as) (map (λ z → z) (map (λ z → z) as))
    ans rewrite mapId as | mapId as = Equivalence.reflexive (Setoid.eq naivePolySetoid)
assoc {a :: as} {[]} {c :: cs} = reflexive ,, ans
  where
    ans : polysEqual (listZip _+_ (λ z → z) (λ z → z) as (map (λ z → z) cs)) (listZip _+_ (λ z → z) (λ z → z) (map (λ z → z) as) cs)
    ans rewrite mapId cs | mapId as = Equivalence.reflexive (Setoid.eq naivePolySetoid)
assoc {a :: as} {b :: bs} {[]} = reflexive ,, ans
  where
    ans : polysEqual (listZip _+_ (λ z → z) (λ z → z) as (map (λ z → z) bs)) (map (λ z → z) (listZip _+_ (λ z → z) (λ z → z) as bs))
    ans rewrite mapId (listZip _+_ id id as bs) | mapId bs = Equivalence.reflexive (Setoid.eq naivePolySetoid)
assoc {a :: as} {b :: bs} {c :: cs} = Group.+Associative G ,, assoc {as} {bs} {cs}

polyGroup : Group naivePolySetoid _+P_
Group.+WellDefined polyGroup = +PwellDefined
Group.0G polyGroup = []
Group.inverse polyGroup = inverse
Group.+Associative polyGroup {a} {b} {c} = assoc {a} {b} {c}
Group.identRight polyGroup = PidentRight
Group.identLeft polyGroup = PidentLeft
Group.invLeft polyGroup {a} = invLeft {a}
Group.invRight polyGroup {a} = invRight {a}

comm : AbelianGroup G → {x y : NaivePoly} → polysEqual (x +P y) (y +P x)
comm com {[]} {y} = Equivalence.transitive (Setoid.eq naivePolySetoid) (Group.identLeft polyGroup) (Equivalence.symmetric (Setoid.eq naivePolySetoid) (Group.identRight polyGroup))
comm com {x :: xs} {[]} = reflexive ,, Equivalence.reflexive (Setoid.eq naivePolySetoid)
comm com {x :: xs} {y :: ys} = AbelianGroup.commutative com ,, comm com {xs} {ys}

abelian : AbelianGroup G → AbelianGroup polyGroup
AbelianGroup.commutative (abelian ab) {x} {y} = comm ab {x} {y}
