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
open import Rings.Definition
open import Vectors
open import Lists.Lists
open import Maybe
open import Rings.Homomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Polynomial.Multiplication {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open Group additiveGroup
open import Groups.Polynomials.Definition additiveGroup
open import Groups.Polynomials.Group additiveGroup
open Setoid S
open Equivalence eq

_*P_ : NaivePoly → NaivePoly → NaivePoly
[] *P b = []
(x :: a) *P [] = []
(x :: a) *P (y :: b) = (x * y) :: ((map (x *_) b) +P (map (y *_) a))

p*Commutative : {a b : NaivePoly} → polysEqual (a *P b) (b *P a)
p*Commutative {[]} {[]} = record {}
p*Commutative {[]} {x :: b} = record {}
p*Commutative {x :: a} {[]} = record {}
p*Commutative {x :: xs} {y :: ys} = *Commutative ,, AbelianGroup.commutative (abelian (record { commutative = Ring.groupIsAbelian R })) {map (_*_ x) ys} {map (_*_ y) xs}

zeroTimes1 : {a : NaivePoly} (c : A) → (c ∼ 0G) → polysEqual (map (_*_ c) a) []
zeroTimes1 {[]} c c=0 = record {}
zeroTimes1 {x :: a} c c=0 = transitive (transitive *Commutative (*WellDefined reflexive c=0)) (timesZero {x}) ,, zeroTimes1 {a} c c=0

zeroTimes2 : {a : NaivePoly} (c : A) → polysEqual a [] → polysEqual (map (_*_ c) a) []
zeroTimes2 {[]} c a=0 = record {}
zeroTimes2 {x :: a} c (fst ,, snd) = transitive (*WellDefined reflexive fst) (timesZero {c}) ,, zeroTimes2 {a} c snd

mapWellDefined : (a c : A) (bs : NaivePoly) → (a ∼ c) → polysEqual (map (_*_ a) bs) (map (_*_ c) bs)
mapWellDefined a c [] a=c = record {}
mapWellDefined a c (x :: bs) a=c = *WellDefined a=c reflexive ,, mapWellDefined a c bs a=c

mapWellDefined' : (a : A) (bs cs : NaivePoly) → polysEqual bs cs → polysEqual (map (_*_ a) bs) (map (_*_ a) cs)
mapWellDefined' a [] [] bs=cs = record {}
mapWellDefined' a [] (x :: cs) (fst ,, snd) = transitive (*WellDefined reflexive fst) (timesZero {a}) ,, Equivalence.symmetric (Setoid.eq naivePolySetoid) (zeroTimes2 {cs} a (Equivalence.symmetric (Setoid.eq naivePolySetoid) snd))
mapWellDefined' a (x :: bs) [] (fst ,, snd) = transitive (*WellDefined reflexive fst) (timesZero {a}) ,, zeroTimes2 {bs} a snd
mapWellDefined' a (b :: bs) (c :: cs) (fst ,, snd) = *WellDefined reflexive fst ,, mapWellDefined' a bs cs snd

*PwellDefinedL : {a b c : NaivePoly} → polysEqual a c → polysEqual (a *P b) (c *P b)
*PwellDefinedL {[]} {[]} {[]} a=c = record {}
*PwellDefinedL {[]} {[]} {x :: c} a=c = record {}
*PwellDefinedL {[]} {x :: b} {[]} a=c = record {}
*PwellDefinedL {[]} {b :: bs} {c :: cs} (fst ,, snd) = transitive (transitive *Commutative (*WellDefined reflexive fst)) (timesZero {b}) ,, Equivalence.symmetric (Setoid.eq naivePolySetoid) (Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined (zeroTimes1 {bs} c fst) (zeroTimes2 {cs} b (Equivalence.symmetric (Setoid.eq naivePolySetoid) snd))) (Group.identLeft polyGroup))
*PwellDefinedL {a :: as} {[]} {[]} a=c = record {}
*PwellDefinedL {a :: as} {[]} {x :: c} a=c = record {}
*PwellDefinedL {a :: as} {b :: bs} {[]} (fst ,, snd) = transitive (transitive *Commutative (*WellDefined reflexive fst)) (timesZero {b}) ,, Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined (zeroTimes1 {bs} a fst) (zeroTimes2 {as} b snd)) (Group.identLeft polyGroup)
*PwellDefinedL {a :: as} {b :: bs} {c :: cs} (fst ,, snd) = *WellDefined fst reflexive ,, +PwellDefined (mapWellDefined a c bs fst) (mapWellDefined' b as cs snd)

*PwellDefinedR : {a b c : NaivePoly} → polysEqual b c → polysEqual (a *P b) (a *P c)
*PwellDefinedR {a} {b} {c} b=c = Equivalence.transitive (Setoid.eq naivePolySetoid) (p*Commutative {a} {b}) (Equivalence.transitive (Setoid.eq naivePolySetoid) (*PwellDefinedL b=c) (p*Commutative {c} {a}))

*PwellDefined : {a b c d : NaivePoly} → polysEqual a c → polysEqual b d → polysEqual (a *P b) (c *P d)
*PwellDefined {a}{b}{c}{d} a=c b=d = Equivalence.transitive (Setoid.eq naivePolySetoid) (*PwellDefinedL a=c) (*PwellDefinedR b=d)

private
  *1 : (a : NaivePoly) → polysEqual (map (_*_ 1R) a) a
  *1 [] = record {}
  *1 (x :: a) = Ring.identIsIdent R ,, *1 a

*Pident : {a : NaivePoly} → polysEqual ((1R :: []) *P a) a
*Pident {[]} = record {}
*Pident {x :: a} = Ring.identIsIdent R ,, (Equivalence.transitive (Setoid.eq naivePolySetoid) (Group.identRight polyGroup {map (_*_ 1R) a}) (*1 a))

private
  mapMap' : (f g : A → A) (xs : NaivePoly) → map f (map g xs) ≡ map (λ x → f (g x)) xs
  mapMap' f g [] = refl
  mapMap' f g (x :: xs) rewrite mapMap' f g xs = refl

  mapDist : (f : A → A) (fDist : {x y : A} → f (x + y) ∼ (f x) + (f y)) (xs ys : NaivePoly) → polysEqual (map f (xs +P ys)) ((map f xs) +P (map f ys))
  mapDist f fDist [] [] = record {}
  mapDist f fDist [] (x :: ys) rewrite mapId ys | mapId (map f ys) = reflexive ,, Equivalence.reflexive (Setoid.eq naivePolySetoid)
  mapDist f fDist (x :: xs) [] rewrite mapId xs | mapId (map f xs) = reflexive ,, Equivalence.reflexive (Setoid.eq naivePolySetoid)
  mapDist f fDist (x :: xs) (y :: ys) = fDist {x} {y} ,, mapDist f fDist xs ys

  mapWd : (f g : A → A) (xs : NaivePoly) → ((x : A) → (f x) ∼ (g x)) → polysEqual (map f xs) (map g xs)
  mapWd f g [] ext = record {}
  mapWd f g (x :: xs) ext = ext x ,, mapWd f g xs ext

  mapDist' : (b c : A) → (as : NaivePoly) → polysEqual (map (_*_ (b + c)) as) (map (_*_ c) as +P map (_*_ b) as)
  mapDist' b c [] = record {}
  mapDist' b c (x :: as) = transitive (Ring.*DistributesOver+' R {b} {c} {x}) groupIsAbelian ,, mapDist' b c as

*Passoc : {a b c : NaivePoly} → polysEqual (a *P (b *P c)) ((a *P b) *P c)
*Passoc {[]} {b} {c} = record {}
*Passoc {a :: as} {[]} {c} = record {}
*Passoc {a :: as} {b :: bs} {[]} = record {}
*Passoc {a :: as} {b :: bs} {c :: cs} = *Associative ,, Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined (mapDist (_*_ a) *DistributesOver+ (map (_*_ b) cs) (map (_*_ c) bs)) (Equivalence.reflexive (Setoid.eq naivePolySetoid))) (Equivalence.transitive (Setoid.eq naivePolySetoid) ans (+PwellDefined (Equivalence.reflexive (Setoid.eq naivePolySetoid) {map (_*_ (a * b)) cs}) (Equivalence.symmetric (Setoid.eq naivePolySetoid) (mapDist (_*_ c) *DistributesOver+ (map (_*_ a) bs) (map (_*_ b) as)))))
  where
    ans : polysEqual (listZip _+_ (λ z → z) (λ z → z) (listZip _+_ (λ z → z) (λ z → z) (map (_*_ a) (map (_*_ b) cs)) (map (_*_ a) (map (_*_ c) bs))) (map (_*_ (b * c)) as)) (listZip _+_ (λ z → z) (λ z → z) (map (_*_ (a * b)) cs) (listZip _+_ (λ z → z) (λ z → z) (map (_*_ c) (map (_*_ a) bs)) (map (_*_ c) (map (_*_ b) as))))
    ans rewrite mapMap' (_*_ a) (_*_ c) bs | mapMap' (_*_ a) (_*_ b) cs | mapMap' (_*_ c) (_*_ a) bs | mapMap' (_*_ c) (_*_ b) as = Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.symmetric (Setoid.eq naivePolySetoid) (Group.+Associative polyGroup {map (λ x → a * (b * x)) cs} {map (λ x → a * (c * x)) bs} {map (_*_ (b * c)) as})) (+PwellDefined {map (λ x → a * (b * x)) cs} {(map (λ x → a * (c * x)) bs) +P map (_*_ (b * c)) as} {(map (_*_ (a * b)) cs)} (mapWd (λ x → a * (b * x)) (_*_ (a * b)) cs λ x → *Associative) (+PwellDefined {map (λ x → a * (c * x)) bs} {map (_*_ (b * c)) as} {map (λ x → c * (a * x)) bs} {map (λ x → c * (b * x)) as} (mapWd (λ x → a * (c * x)) (λ x → c * (a * x)) bs λ x → transitive *Commutative (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative))) (mapWd (_*_ (b * c)) (λ x → c * (b * x)) as λ x → transitive (*WellDefined *Commutative reflexive) (symmetric *Associative))))

*Pdistrib : {a b c : NaivePoly} → polysEqual (a *P (b +P c)) ((a *P b) +P (a *P c))
*Pdistrib {[]} {b} {c} = record {}
*Pdistrib {a :: as} {[]} {[]} = record {}
*Pdistrib {a :: as} {[]} {c :: cs} = reflexive ,, ans
  where
    ans : polysEqual (listZip _+_ (λ z → z) (λ z → z) (map (_*_ a) (map (λ z → z) cs)) (map (_*_ c) as)) (map (λ z → z) (listZip _+_ (λ z → z) (λ z → z) (map (_*_ a) cs) (map (_*_ c) as)))
    ans rewrite mapId (listZip _+_ id id (map (_*_ a) cs) (map (_*_ c) as)) | mapId cs = Equivalence.reflexive (Setoid.eq naivePolySetoid)
*Pdistrib {a :: as} {b :: bs} {[]} = reflexive ,, ans
  where
    ans : polysEqual (listZip _+_ (λ z → z) (λ z → z) (map (_*_ a) (map (λ z → z) bs)) (map (_*_ b) as)) (map (λ z → z) (listZip _+_ (λ z → z) (λ z → z) (map (_*_ a) bs) (map (_*_ b) as)))
    ans rewrite mapId (listZip _+_ id id (map (_*_ a) bs) (map (_*_ b) as)) | mapId bs = Equivalence.reflexive (Setoid.eq naivePolySetoid)
*Pdistrib {a :: as} {b :: bs} {c :: cs} = *DistributesOver+ ,, Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined {map (_*_ a) (bs +P cs)} {map (_*_ (b + c)) as} {(map (_*_ a) bs) +P (map (_*_ a) cs)} (mapDist (_*_ a) *DistributesOver+ bs cs) (mapDist' b c as)) (Group.+Associative polyGroup {(map (_*_ a) bs) +P (map (_*_ a) cs)} {map (_*_ c) as} {map (_*_ b) as})) (+PwellDefined (Equivalence.symmetric (Setoid.eq naivePolySetoid) (Group.+Associative polyGroup {map (_*_ a) bs} {map (_*_ a) cs} {map (_*_ c) as})) (Equivalence.reflexive (Setoid.eq naivePolySetoid) {map (_*_ b) as}))) (Equivalence.symmetric (Setoid.eq naivePolySetoid) (Group.+Associative polyGroup {map (_*_ a) bs} {(map (_*_ a) cs) +P (map (_*_ c) as)} {map (_*_ b) as}))) (+PwellDefined (Equivalence.reflexive (Setoid.eq naivePolySetoid) {map (_*_ a) bs}) (AbelianGroup.commutative (abelian (record { commutative = groupIsAbelian })) {map (_*_ a) cs +P map (_*_ c) as} {map (_*_ b) as}))) (Group.+Associative polyGroup {map (_*_ a) bs} {map (_*_ b) as})
