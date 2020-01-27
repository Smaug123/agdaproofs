{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Abelian.Definition
open import Groups.Definition
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Lists.Lists


module Groups.Polynomials.Addition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Groups.Polynomials.Definition G
open Setoid S
open Equivalence eq
open Group G

_+P_ : NaivePoly → NaivePoly → NaivePoly
_+P_ = listZip _+_ id id

inverse' : NaivePoly → NaivePoly
inverse' = map (Group.inverse G)

abstract
  PidentRight : {m : NaivePoly} → polysEqual (m +P []) m
  PidentRight {[]} = record {}
  PidentRight {x :: m} = reflexive ,, identityOfIndiscernablesLeft polysEqual (Equivalence.reflexive (Setoid.eq naivePolySetoid)) (equalityCommutative (mapId m))

  +PwellDefined : {m n x y : NaivePoly} → polysEqual m x → polysEqual n y → polysEqual (m +P n) (x +P y)
  +PwellDefined {[]} {[]} {[]} {[]} m=x n=y = record {}
  +PwellDefined {[]} {[]} {[]} {x :: y} m=x (fst ,, snd) = fst ,, identityOfIndiscernablesRight polysEqual snd (equalityCommutative (mapId y))
  +PwellDefined {[]} {[]} {x :: xs} {[]} (fst ,, snd) n=y = fst ,, identityOfIndiscernablesRight polysEqual snd (equalityCommutative (mapId xs))
  +PwellDefined {[]} {[]} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identRight ,, +PwellDefined {[]} {[]} {xs} {ys} snd snd2
  +PwellDefined {[]} {n :: ns} {[]} {[]} m=x (fst ,, snd) = fst ,, identityOfIndiscernablesLeft polysEqual snd (equalityCommutative (mapId ns))
  +PwellDefined {[]} {n :: ns} {[]} {y :: ys} m=x (fst ,, snd) = fst ,, +PwellDefined m=x snd
  +PwellDefined {[]} {n :: ns} {x :: xs} {[]} (fst ,, snd) (fst2 ,, snd2) = transitive fst2 (symmetric fst) ,, ans
    where
      ans : polysEqual (map (λ z → z) ns) (map (λ z → z) xs)
      ans rewrite mapId ns | mapId xs = Equivalence.transitive (Setoid.eq naivePolySetoid) snd2 snd
  +PwellDefined {[]} {n :: ns} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (symmetric identLeft) (+WellDefined (symmetric fst) fst2) ,, (+PwellDefined snd snd2)
  +PwellDefined {m :: ms} {[]} {[]} {[]} (fst ,, snd) _ = fst ,, identityOfIndiscernablesLeft polysEqual snd (equalityCommutative (mapId ms))
  +PwellDefined {m :: ms} {[]} {[]} {x :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive fst (symmetric fst2) ,, ans
    where
      ans : polysEqual (map (λ z → z) ms) (map (λ z → z) ys)
      ans rewrite mapId ms | mapId ys = Equivalence.transitive (Setoid.eq naivePolySetoid) snd snd2
  +PwellDefined {m :: ms} {[]} {x :: xs} {[]} (fst ,, snd) n=y = fst ,, ans
    where
      ans : polysEqual (map (λ z → z) ms) (map (λ z → z) xs)
      ans rewrite mapId ms | mapId xs = snd
  +PwellDefined {m :: ms} {[]} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (symmetric identRight) (+WellDefined fst (symmetric fst2)) ,, identityOfIndiscernablesLeft polysEqual (Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.symmetric (Setoid.eq naivePolySetoid) PidentRight) (+PwellDefined snd snd2)) (equalityCommutative (mapId ms))
  +PwellDefined {m :: ms} {n :: ns} {[]} {[]} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identLeft ,, +PwellDefined snd snd2
  +PwellDefined {m :: ms} {n :: ns} {[]} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identLeft ,, +PwellDefined snd snd2
  +PwellDefined {m :: ms} {n :: ns} {x :: xs} {[]} (fst ,, snd) (fst2 ,, snd2) = transitive (+WellDefined fst fst2) identRight ,, identityOfIndiscernablesRight polysEqual (Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined snd snd2) PidentRight) (equalityCommutative (mapId xs))
  +PwellDefined {m :: ms} {n :: ns} {x :: xs} {y :: ys} (fst ,, snd) (fst2 ,, snd2) = +WellDefined fst fst2 ,, +PwellDefined snd snd2

  PidentLeft : {m : NaivePoly} → polysEqual ([] +P m) m
  PidentLeft {[]} = record {}
  PidentLeft {x :: m} = reflexive ,, identityOfIndiscernablesLeft polysEqual (Equivalence.reflexive (Setoid.eq naivePolySetoid)) (equalityCommutative (mapId m))

  invLeft' : {a : NaivePoly} → polysEqual ((inverse' a) +P a) []
  invLeft' {[]} = record {}
  invLeft' {x :: a} = Group.invLeft G ,, invLeft' {a}

  invRight' : {a : NaivePoly} → polysEqual (a +P (inverse' a)) []
  invRight' {[]} = record {}
  invRight' {x :: a} = Group.invRight G ,, invRight' {a}

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

  comm : AbelianGroup G → {x y : NaivePoly} → polysEqual (x +P y) (y +P x)
  comm com {[]} {y} = Equivalence.transitive (Setoid.eq naivePolySetoid) PidentLeft (Equivalence.symmetric (Setoid.eq naivePolySetoid) PidentRight)
  comm com {x :: xs} {[]} = reflexive ,, Equivalence.reflexive (Setoid.eq naivePolySetoid)
  comm com {x :: xs} {y :: ys} = AbelianGroup.commutative com ,, comm com {xs} {ys}

  mapDist : (f : A → A) (fDist : {x y : A} → f (x + y) ∼ (f x) + (f y)) (xs ys : NaivePoly) → polysEqual (map f (xs +P ys)) ((map f xs) +P (map f ys))
  mapDist f fDist [] [] = record {}
  mapDist f fDist [] (x :: ys) rewrite mapId ys | mapId (map f ys) = reflexive ,, Equivalence.reflexive (Setoid.eq naivePolySetoid)
  mapDist f fDist (x :: xs) [] rewrite mapId xs | mapId (map f xs) = reflexive ,, Equivalence.reflexive (Setoid.eq naivePolySetoid)
  mapDist f fDist (x :: xs) (y :: ys) = fDist {x} {y} ,, mapDist f fDist xs ys
