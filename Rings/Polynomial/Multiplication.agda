{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Setoids.Setoids
open import Functions.Definition
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Lists.Lists

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
(x :: a) *P (y :: b) = (x * y) :: (((map (x *_) b) +P (map (y *_) a)) +P (0R :: (a *P b)))

abstract
  +PCommutative : {x y : NaivePoly} → polysEqual (x +P y) (y +P x)
  +PCommutative {x} {y} = comm (record { commutative = groupIsAbelian }) {x} {y}

  p*Commutative : {a b : NaivePoly} → polysEqual (a *P b) (b *P a)
  p*Commutative {[]} {[]} = record {}
  p*Commutative {[]} {x :: b} = record {}
  p*Commutative {x :: a} {[]} = record {}
  p*Commutative {x :: xs} {y :: ys} = *Commutative ,, +PwellDefined (+PCommutative {map (_*_ x) ys} {map (_*_ y) xs}) (reflexive ,, p*Commutative {xs} {ys})

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
  *PwellDefinedL {[]} {b :: bs} {c :: cs} (fst ,, snd) = transitive (transitive *Commutative (*WellDefined reflexive fst)) (timesZero {b}) ,, Equivalence.transitive (Setoid.eq naivePolySetoid) (Equivalence.transitive (Setoid.eq naivePolySetoid) {_} {(map (_*_ c) bs) +P (0G :: (cs *P bs))} (Equivalence.transitive (Setoid.eq naivePolySetoid) {_} {[] +P (0G :: (cs *P bs))} (reflexive ,, ans) (+PwellDefined (Equivalence.symmetric (Setoid.eq naivePolySetoid) (zeroTimes1 {bs} c fst)) (Equivalence.reflexive (Setoid.eq naivePolySetoid) {0G :: (cs *P bs)}))) (+PwellDefined (Equivalence.symmetric (Setoid.eq naivePolySetoid) (Group.identRight polyGroup {map (_*_ c) bs})) (Equivalence.reflexive (Setoid.eq naivePolySetoid) {0G :: (cs *P bs)}))) (+PwellDefined {(map (_*_ c) bs +P [])} {0G :: (cs *P bs)} {(map (_*_ c) bs) +P map (_*_ b) cs} (+PwellDefined (Equivalence.reflexive (Setoid.eq naivePolySetoid) {map (_*_ c) bs}) (Equivalence.symmetric (Setoid.eq naivePolySetoid) (zeroTimes2 {cs} b (Equivalence.symmetric (Setoid.eq naivePolySetoid) snd)))) (Equivalence.reflexive (Setoid.eq naivePolySetoid) {0G :: (cs *P bs)}))
    where
      ans : polysEqual [] (map id (cs *P bs))
      ans rewrite mapId (cs *P bs) = *PwellDefinedL snd
  *PwellDefinedL {a :: as} {[]} {[]} a=c = record {}
  *PwellDefinedL {a :: as} {[]} {x :: c} a=c = record {}
  *PwellDefinedL {a :: as} {b :: bs} {[]} (fst ,, snd) = transitive (transitive *Commutative (*WellDefined reflexive fst)) (timesZero {b}) ,, Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined {(map (_*_ a) bs +P map (_*_ b) as)} {0G :: (as *P bs)} {[] +P []} {[]} (+PwellDefined {map (_*_ a) bs} {map (_*_ b) as} {[]} {[]} (zeroTimes1 {bs} a fst) (zeroTimes2 {as} b snd)) (reflexive ,, *PwellDefinedL {as} {bs} {[]} snd)) (record {})
  *PwellDefinedL {a :: as} {b :: bs} {c :: cs} (fst ,, snd) = *WellDefined fst reflexive ,, +PwellDefined {(map (_*_ a) bs) +P (map (_*_ b) as)} {0G :: (as *P bs)} {map (_*_ c) bs +P map (_*_ b) cs} {0G :: (cs *P bs)} (+PwellDefined {map (_*_ a) bs} {map (_*_ b) as} {map (_*_ c) bs} {map (_*_ b) cs} (mapWellDefined a c bs fst) (mapWellDefined' b as cs snd)) (reflexive ,, *PwellDefinedL {as} {bs} {cs} snd)

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
  *Pident {x :: a} = Ring.identIsIdent R ,, Equivalence.transitive (Setoid.eq naivePolySetoid) (+PwellDefined {map (_*_ 1R) a +P []} {0G :: []} {map (_*_ 1R) a} {[]} (Group.identRight polyGroup) (reflexive ,, record {})) (Equivalence.transitive (Setoid.eq naivePolySetoid) (Group.identRight polyGroup {map (_*_ 1R) a}) (*1 a))

  private
    mapMap' : (f g : A → A) (xs : NaivePoly) → map f (map g xs) ≡ map (λ x → f (g x)) xs
    mapMap' f g [] = refl
    mapMap' f g (x :: xs) rewrite mapMap' f g xs = refl

    mapMap'' : (f g : A → A) (xs : NaivePoly) → Setoid._∼_ naivePolySetoid (map f (map g xs)) (map (λ x → f (g x)) xs)
    mapMap'' f g xs rewrite mapMap' f g xs = Equivalence.reflexive (Setoid.eq naivePolySetoid)

    mapWd : (f g : A → A) (xs : NaivePoly) → ((x : A) → (f x) ∼ (g x)) → polysEqual (map f xs) (map g xs)
    mapWd f g [] ext = record {}
    mapWd f g (x :: xs) ext = ext x ,, mapWd f g xs ext

    mapDist' : (b c : A) → (as : NaivePoly) → polysEqual (map (_*_ (b + c)) as) (map (_*_ c) as +P map (_*_ b) as)
    mapDist' b c [] = record {}
    mapDist' b c (x :: as) = transitive (Ring.*DistributesOver+' R {b} {c} {x}) groupIsAbelian ,, mapDist' b c as

    mapTimes : (a b : NaivePoly) (c : A) → polysEqual (a *P (map (_*_ c) b)) (map (_*_ c) (a *P b))
    mapTimes [] b c = record {}
    mapTimes (a :: as) [] c = record {}
    mapTimes (a :: as) (x :: b) c = transitive *Associative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)) ,, trans (+PwellDefined {(map (_*_ a) (map (_*_ c) b)) +P map (_*_ (c * x)) as} {0G :: (as *P map (_*_ c) b)} {map (_*_ c) (map (_*_ a) b +P map (_*_ x) as)} (trans (+PwellDefined {map (_*_ a) (map (_*_ c) b)} {map (_*_ (c * x)) as} {map (_*_ c) (map (_*_ a) b)} (trans (mapMap'' (_*_ a) (_*_ c) b) (trans (mapWd (λ x → a * (c * x)) (λ x → c * (a * x)) b (λ x → transitive *Associative (transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)))) (sym (mapMap'' (_*_ c) (_*_ a) b)))) (trans (mapWd (_*_ (c * x)) (λ y → c * (x * y)) as λ y → symmetric *Associative) (sym (mapMap'' (_*_ c) (_*_ x) as)))) (sym (mapDist (_*_ c) *DistributesOver+ (map (_*_ a) b) (map (_*_ x) as)))) (symmetric timesZero ,, mapTimes as b c)) (sym (mapDist (_*_ c) *DistributesOver+ (map (_*_ a) b +P map (_*_ x) as) (0G :: (as *P b))))
      where
        open Equivalence (Setoid.eq naivePolySetoid) renaming (transitive to trans ; symmetric to sym ; reflexive to ref)

    mapTimes' : (a b : NaivePoly) (c : A) → polysEqual (map (_*_ c) (a *P b)) ((map (_*_ c) a) *P b)
    mapTimes' a b c = trans (trans (mapWellDefined' c (a *P b) (b *P a) (p*Commutative {a} {b})) (sym (mapTimes b a c))) (p*Commutative {b} {map (_*_ c) a})
      where
        open Equivalence (Setoid.eq naivePolySetoid) renaming (transitive to trans ; symmetric to sym ; reflexive to ref)

  bumpTimes' : (a bs : NaivePoly) (b : A) → polysEqual (a *P (b :: bs)) (map (_*_ b) a +P (0G :: (a *P bs)))
  bumpTimes' [] bs b = reflexive ,, record {}
  bumpTimes' (x :: a) bs b = transitive *Commutative (symmetric identRight) ,, trans (+PwellDefined {map (_*_ x) bs +P map (_*_ b) a} {0G :: (a *P bs)} {_} {0G :: (a *P bs)} (+PCommutative {map (_*_ x) bs} {map (_*_ b) a}) (ref {0G :: (a *P bs)})) (trans (sym (Group.+Associative polyGroup {map (_*_ b) a})) (+PwellDefined {map (_*_ b) a} {_} {map (_*_ b) a} {_} (ref {map (_*_ b) a}) (trans (trans (+PwellDefined {map (_*_ x) bs} {_} {map (_*_ x) bs} (ref {map (_*_ x) bs}) (reflexive ,, p*Commutative {a})) (sym (bumpTimes' bs a x))) (p*Commutative {bs}))))
    where
      open Equivalence (Setoid.eq naivePolySetoid) renaming (transitive to trans ; symmetric to sym ; reflexive to ref)

  bumpTimes : {a b : NaivePoly} → polysEqual (a *P (0G :: b)) (0G :: (a *P b))
  bumpTimes {[]} {b} = reflexive ,, record {}
  bumpTimes {x :: a} {[]} = timesZero ,, trans (sym (Group.+Associative polyGroup {[]} {map (_*_ 0G) a})) ans
    where
      open Equivalence (Setoid.eq naivePolySetoid) renaming (transitive to trans ; symmetric to sym ; reflexive to ref)
      ans : polysEqual (map id (map (_*_ 0G) a +P (0G :: (a *P [])))) []
      ans rewrite mapId (map (_*_ 0G) a +P (0G :: (a *P []))) = (+PwellDefined {map (_*_ 0G) a} {0G :: (a *P [])} {[]} {[]} (zeroTimes1 0G reflexive) (reflexive ,, p*Commutative {a}))
  bumpTimes {x :: a} {b :: bs} = timesZero ,, trans (+PwellDefined {((x * b) :: map (_*_ x) bs) +P map (_*_ 0G) a} {0G :: (a *P (b :: bs))} {(x * b) :: map (_*_ x) bs} {0G :: (a *P (b :: bs))} (trans (+PwellDefined {(x * b) :: map (_*_ x) bs} {map (_*_ 0G) a} {(x * b) :: map (_*_ x) bs} {[]} (ref {(x * b) :: map (_*_ x) bs}) (zeroTimes1 0G reflexive)) (Group.identRight polyGroup {(x * b) :: map (_*_ x) bs})) (ref {0G :: (a *P (b :: bs))})) (identRight ,, trans (+PwellDefined {map (_*_ x) bs} {_} {map (_*_ x) bs} ref (bumpTimes' a bs b)) (Group.+Associative polyGroup {map (_*_ x) bs} {map (_*_ b) a} {0G :: (a *P bs)}))
    where
      open Equivalence (Setoid.eq naivePolySetoid) renaming (transitive to trans ; symmetric to sym ; reflexive to ref)

  *Pdistrib : {a b c : NaivePoly} → polysEqual (a *P (b +P c)) ((a *P b) +P (a *P c))
  *Pdistrib {[]} {b} {c} = record {}
  *Pdistrib {a :: as} {[]} {[]} = record {}
  *Pdistrib {a :: as} {[]} {c :: cs} rewrite mapId cs | mapId ((map (_*_ a) cs +P map (_*_ c) as) +P (0G :: (as *P cs))) = reflexive ,, +PwellDefined {(map (_*_ a) cs) +P (map (_*_ c) as)} {_} {(map (_*_ a) cs) +P (map (_*_ c) as)} (Equivalence.reflexive (Setoid.eq naivePolySetoid)) (Equivalence.reflexive (Setoid.eq naivePolySetoid) {0G :: (as *P cs)})
  *Pdistrib {a :: as} {b :: bs} {[]} rewrite mapId bs | mapId ((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) = reflexive ,, +PwellDefined {(map (_*_ a) bs) +P (map (_*_ b) as)} {_} {(map (_*_ a) bs) +P (map (_*_ b) as)} (Equivalence.reflexive (Setoid.eq naivePolySetoid)) (Equivalence.reflexive (Setoid.eq naivePolySetoid) {0G :: (as *P bs)})
  *Pdistrib {a :: as} {b :: bs} {c :: cs} = *DistributesOver+ ,, trans (+PwellDefined {(map (_*_ a) (bs +P cs)) +P (map (_*_ (b + c)) as)} {0G :: (as *P (bs +P cs))} {(map (_*_ a) bs +P map (_*_ b) as) +P ((map (_*_ a) cs) +P (map (_*_ c) as))} {0G :: ((as *P bs) +P (as *P cs))} (trans (+PwellDefined (mapDist (_*_ a) *DistributesOver+ bs cs) (mapDist' b c as)) (trans (sym (+Assoc {map (_*_ a) bs} {map (_*_ a) cs})) (trans (+PwellDefined (ref {map (_*_ a) bs}) (trans (trans (+Assoc {map (_*_ a) cs} {map (_*_ c) as}) ref) (+PCommutative {map (_*_ a) cs +P map (_*_ c) as} {map (_*_ b) as}))) (+Assoc {map (_*_ a) bs} {map (_*_ b) as})))) (reflexive ,, *Pdistrib {as} {bs} {cs})) (trans (sym (+Assoc {(map (_*_ a) bs +P map (_*_ b) as)} {(map (_*_ a) cs +P map (_*_ c) as)} {0G :: ((as *P bs) +P (as *P cs))})) (trans (+PwellDefined (ref {map (_*_ a) bs +P map (_*_ b) as}) (trans (trans (+PwellDefined (ref {map (_*_ a) cs +P map (_*_ c) as}) (symmetric identLeft ,, +PCommutative {as *P bs})) (+Assoc {map (_*_ a) cs +P (map (_*_ c) as)} {0G :: (as *P cs)} {0G :: (as *P bs)})) (+PCommutative {(map (_*_ a) cs +P map (_*_ c) as) +P (0G :: (as *P cs))} {0G :: (as *P bs)}))) (+Assoc {map (_*_ a) bs +P map (_*_ b) as} {0G :: (as *P bs)})))
    where
      open Equivalence (Setoid.eq naivePolySetoid) renaming (transitive to trans ; symmetric to sym ; reflexive to ref)
      open Group polyGroup renaming (+Associative to +Assoc ; 0G to 0P) hiding (identLeft)

*Passoc : {a b c : NaivePoly} → polysEqual (a *P (b *P c)) ((a *P b) *P c)
*Passoc {[]} {b} {c} = record {}
*Passoc {a :: as} {[]} {c} = record {}
*Passoc {a :: as} {b :: bs} {[]} = record {}
*Passoc {a :: as} {b :: bs} {c :: cs} = *Associative ,, trans (+PwellDefined {(map (_*_ a) ((map (_*_ b) cs +P map (_*_ c) bs) +P (0G :: (bs *P cs))) +P map (_*_ (b * c)) as)} {0G :: (as *P ((map (_*_ b) cs +P map (_*_ c) bs) +P (0G :: (bs *P cs))))} {(((map (_*_ (a * b)) cs) +P (map (_*_ (a * c)) bs)) +P (map (_*_ a) (0G :: (bs *P cs)))) +P (map (_*_ (b * c)) as)} {0G :: (((map (_*_ b) (as *P cs)) +P (map (_*_ c) (as *P bs))) +P (as *P (0G :: (bs *P cs))))} (+PwellDefined {map (_*_ a) ((map (_*_ b) cs +P map (_*_ c) bs) +P (0G :: (bs *P cs)))} {map (_*_ (b * c)) as} {((map (_*_ (a * b)) cs +P map (_*_ (a * c)) bs) +P ((a * 0G) :: map (_*_ a) (bs *P cs)))} {map (_*_ (b * c)) as} (trans (mapDist (_*_ a) *DistributesOver+ (map (_*_ b) cs +P map (_*_ c) bs) (0G :: (bs *P cs))) (+PwellDefined {map (_*_ a) (map (_*_ b) cs +P map (_*_ c) bs)} {(a * 0G) :: map (_*_ a) (bs *P cs)} {map (_*_ (a * b)) cs +P map (_*_ (a * c)) bs} (trans (mapDist (_*_ a) *DistributesOver+ (map (_*_ b) cs) (map (_*_ c) bs)) (+PwellDefined {map (_*_ a) (map (_*_ b) cs)} {map (_*_ a) (map (_*_ c) bs)} {map (_*_ (a * b)) cs} (trans (mapMap'' (_*_ a) (_*_ b) cs) (mapWd (λ x → a * (b * x)) (_*_ (a * b)) cs (λ x → *Associative))) (trans (mapMap'' (_*_ a) (_*_ c) bs) (mapWd (λ x → a * (c * x)) (_*_ (a * c)) bs λ x → *Associative)))) (ref {(a * 0G) :: map (_*_ a) (bs *P cs)}))) (ref {map (_*_ (b * c)) as})) (reflexive ,, trans (*Pdistrib {as} {(map (_*_ b) cs +P map (_*_ c) bs)} {0G :: (bs *P cs)}) (+PwellDefined {(as *P (map (_*_ b) cs +P map (_*_ c) bs))} {as *P (0G :: (bs *P cs))} {(map (_*_ b) (as *P cs) +P map (_*_ c) (as *P bs))} (trans (*Pdistrib {as} {map (_*_ b) cs} {map (_*_ c) bs}) (+PwellDefined {as *P map (_*_ b) cs} {as *P map (_*_ c) bs} {map (_*_ b) (as *P cs)} (mapTimes as cs b) (mapTimes as bs c))) (ref {as *P (0G :: (bs *P cs))})))) (trans (trans (sym (Group.+Associative polyGroup {((map (_*_ (a * b)) cs) +P (map (_*_ (a * c)) bs)) +P ((a * 0G) :: map (_*_ a) (bs *P cs))})) (trans (sym (Group.+Associative polyGroup {(map (_*_ (a * b)) cs) +P (map (_*_ (a * c)) bs)})) (trans (sym (Group.+Associative polyGroup {map (_*_ (a * b)) cs})) (+PwellDefined {map (_*_ (a * b)) cs} (ref {map (_*_ (a * b)) cs}) (trans (trans ans (Group.+Associative polyGroup {map (_*_ c) (map (_*_ a) bs +P map (_*_ b) as)})) (+PwellDefined {_} {0G :: (((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) *P cs)} {map (_*_ c) ((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs)))} (sym (mapDist (_*_ c) *DistributesOver+ ((map (_*_ a) bs +P map (_*_ b) as)) (0G :: (as *P bs)))) (ref {0G :: (((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) *P cs)}))))))) (Group.+Associative polyGroup {map (_*_ (a * b)) cs} {map (_*_ c) ((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs)))}))
  where
    open Equivalence (Setoid.eq naivePolySetoid) renaming (transitive to trans ; symmetric to sym ; reflexive to ref)
    open Group polyGroup renaming (+Associative to +Assoc ; 0G to 0P) hiding (identLeft ; identRight)
    ans2 : polysEqual ((map (_*_ a) (bs *P cs) +P (map (_*_ b) (as *P cs) +P map (_*_ c) (as *P bs))) +P (as *P (0G :: (bs *P cs)))) (map (_*_ c) (as *P bs) +P (((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) *P cs))
    ans2 = trans (+PwellDefined {_} {as *P (0G :: (bs *P cs))} {_} {as *P (0G :: (bs *P cs))} (trans (+Assoc {map (_*_ a) (bs *P cs)} {map (_*_ b) (as *P cs)} {map (_*_ c) (as *P bs)}) (+PCommutative {map (_*_ a) (bs *P cs) +P map (_*_ b) (as *P cs)} {map (_*_ c) (as *P bs)})) ref) (trans (sym (+Assoc {map (_*_ c) (as *P bs)} {_} {as *P (0G :: (bs *P cs))}) ) (+PwellDefined {map (_*_ c) (as *P bs)} {_} {map (_*_ c) (as *P bs)} ref (trans (+PwellDefined {map (_*_ a) (bs *P cs) +P map (_*_ b) (as *P cs)} {as *P (0G :: (bs *P cs))} {((map (_*_ a) bs) *P cs) +P ((map (_*_ b) as) *P cs)} {0G :: (as *P (bs *P cs))} (+PwellDefined {map (_*_ a) (bs *P cs)} {map (_*_ b) (as *P cs)} {map (_*_ a) bs *P cs} {map (_*_ b) as *P cs} (mapTimes' bs cs a) (mapTimes' as cs b)) (bumpTimes {as} {bs *P cs})) (trans (trans (+PwellDefined {(map (_*_ a) bs *P cs) +P (map (_*_ b) as *P cs)} {0G :: (as *P (bs *P cs))} {cs *P (map (_*_ a) bs +P map (_*_ b) as)} {cs *P (0G :: (as *P bs))} (trans (+PwellDefined {map (_*_ a) bs *P cs} {map (_*_ b) as *P cs} {cs *P map (_*_ a) bs} {cs *P map (_*_ b) as} (p*Commutative {_} {cs}) (p*Commutative {_} {cs})) (sym (*Pdistrib {cs} {map (_*_ a) bs} {map (_*_ b) as}))) (trans (reflexive ,, trans (*Passoc {as} {bs} {cs}) (p*Commutative {_} {cs})) (sym (bumpTimes {cs} {as *P bs})))) (sym (*Pdistrib {cs} {(map (_*_ a) bs) +P (map (_*_ b) as)} {0G :: (as *P bs)}))) (p*Commutative {cs} {(map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))})))))
    ans :
      polysEqual
        ((map (_*_ (a * c)) bs) +P (((a * 0G) :: map (_*_ a) (bs *P cs)) +P (map (_*_ (b * c)) as +P (0G :: ((map (_*_ b) (as *P cs) +P map (_*_ c) (as *P bs)) +P (as *P (0G :: (bs *P cs))))))))
        ((map (_*_ c) ((map (_*_ a) bs) +P (map (_*_ b) as))) +P (((c * 0G) :: map (_*_ c) (as *P bs)) +P (0G :: (((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) *P cs))))
    ans = trans (trans (+PwellDefined {map (_*_ (a * c)) bs} {_} {map (_*_ c) (map (_*_ a) bs)} (trans (mapWd (_*_ (a * c)) (λ x → c * (a * x)) bs (λ x → transitive (*WellDefined *Commutative reflexive) (symmetric *Associative))) (sym (mapMap'' (_*_ c) (_*_ a) bs))) (trans (+PCommutative {(a * 0G) :: map (_*_ a) (bs *P cs)} {map (_*_ (b * c)) as +P (0G :: ((map (_*_ b) (as *P cs) +P map (_*_ c) (as *P bs)) +P (as *P (0G :: bs *P cs))))}) (trans (sym (+Assoc {map (_*_ (b * c)) as})) (+PwellDefined {map (_*_ (b * c)) as} {_} {map (_*_ c) (map (_*_ b) as)} (trans (mapWd (_*_ (b * c)) (λ x → c * (b * x)) as λ x → transitive (*WellDefined *Commutative reflexive) (symmetric *Associative)) (sym (mapMap'' (_*_ c) (_*_ b) as))) (transitive identLeft (transitive (transitive timesZero (symmetric timesZero)) (symmetric identRight)) ,, trans (+PCommutative {(map (_*_ b) (as *P cs) +P map (_*_ c) (as *P bs)) +P (as *P (0G :: (bs *P cs)))} {map (_*_ a) (bs *P cs)}) (trans (+Assoc {map (_*_ a) (bs *P cs)} {(map (_*_ b) (as *P cs)) +P (map (_*_ c) (as *P bs))} {as *P (0G :: (bs *P cs))}) ans2)))))) (+Assoc {map (_*_ c) (map (_*_ a) bs)})) (+PwellDefined {(map (_*_ c) (map (_*_ a) bs)) +P (map (_*_ c) (map (_*_ b) as))} {(((c * 0G) :: map (_*_ c) (as *P bs)) +P (0G :: (((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) *P cs)))} {map (_*_ c) ((map (_*_ a) bs) +P (map (_*_ b) as))} {(((c * 0G) :: map (_*_ c) (as *P bs)) +P (0G :: (((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) *P cs)))} (sym (mapDist (_*_ c) (*DistributesOver+) (map (_*_ a) bs) (map (_*_ b) as))) (ref {(((c * 0G) :: map (_*_ c) (as *P bs)) +P (0G :: (((map (_*_ a) bs +P map (_*_ b) as) +P (0G :: (as *P bs))) *P cs)))}))
