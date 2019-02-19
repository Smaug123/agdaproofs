{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals
open import Lists
open import Setoids.Setoids
open import Functions

module Setoids.Lists where
  listEquality : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Rel {a} {b} (List A)
  listEquality S [] [] = True'
  listEquality S [] (x :: w2) = False'
  listEquality S (x :: w1) [] = False'
  listEquality S (x :: w1) (y :: w2) = (Setoid._∼_ S x y) && listEquality S w1 w2

  listEqualityReflexive : {a b : _} {A : Set a} (S : Setoid {a} {b} A) (w : List A) → listEquality S w w
  listEqualityReflexive S [] = record {}
  listEqualityReflexive S (x :: w) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)) ,, listEqualityReflexive S w

  listEqualitySymmetric : {a b : _} {A : Set a} (S : Setoid {a} {b} A) {w1 w2 : List A} → listEquality S w1 w2 → listEquality S w2 w1
  listEqualitySymmetric S {w1 = []} {[]} pr = record {}
  listEqualitySymmetric S {[]} {x :: xs} ()
  listEqualitySymmetric S {x :: xs} {[]} ()
  listEqualitySymmetric S {w1 = x :: w1} {y :: w2} (pr1 ,, pr2) = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) pr1 ,, listEqualitySymmetric S pr2

  listEqualityTransitive : {a b : _} {A : Set a} (S : Setoid {a} {b} A) {w1 w2 w3 : List A} → listEquality S w1 w2 → listEquality S w2 w3 → listEquality S w1 w3
  listEqualityTransitive S {w1 = []} {[]} {[]} w1=w2 w2=w3 = record {}
  listEqualityTransitive S {w1 = []} {[]} {x :: xs} w1=w2 ()
  listEqualityTransitive S {w1 = []} {x :: xs} {w3} () w2=w3
  listEqualityTransitive S {w1 = x :: w1} {[]} {w3} () w2=w3
  listEqualityTransitive S {w1 = x :: w1} {y :: ys} {[]} w1=w2 ()
  listEqualityTransitive S {w1 = x :: w1} {y :: w2} {z :: w3} (pr1 ,, pr2) (pr3 ,, pr4) = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) pr1 pr3 ,, listEqualityTransitive S pr2 pr4

  listEqualityRespectsMap : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) (fWD : {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)) → {w1 w2 : List A} (w1=w2 : listEquality S w1 w2) → listEquality T (listMap f w1) (listMap f w2)
  listEqualityRespectsMap S T f fWD {[]} {[]} w1=w2 = record {}
  listEqualityRespectsMap S T f fWD {[]} {x :: w2} ()
  listEqualityRespectsMap S T f fWD {x :: w1} {[]} ()
  listEqualityRespectsMap S T f fWD {x :: w1} {y :: w2} (x=y ,, w1=w2) = fWD x=y ,, listEqualityRespectsMap S T f fWD {w1} {w2} w1=w2

  listSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (List A)
  Setoid._∼_ (listSetoid S) word1 word2 = listEquality S word1 word2
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (listSetoid S))) {word} = listEqualityReflexive S word
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (listSetoid S))) pr = listEqualitySymmetric S pr
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (listSetoid S))) pr1 pr2 = listEqualityTransitive S pr1 pr2

  consWellDefined : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (xs : List A) {x y : A} (x=y : Setoid._∼_ S x y) → Setoid._∼_ (listSetoid S) (x :: xs) (y :: xs)
  consWellDefined {S = S} xs x=y = x=y ,, Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (listSetoid S)))

  appendWellDefined : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {xs ys as bs : List A} (xs=as : Setoid._∼_ (listSetoid S) xs as) → (ys=bs : Setoid._∼_ (listSetoid S) ys bs) → Setoid._∼_ (listSetoid S) (xs ++ ys) (as ++ bs)
  appendWellDefined {S = S} {[]} {[]} {[]} {[]} record {} record {} = record {}
  appendWellDefined {S = S} {[]} {[]} {[]} {x :: bs} record {} ()
  appendWellDefined {S = S} {[]} {x :: ys} {[]} {[]} record {} ys=bs = ys=bs
  appendWellDefined {S = S} {[]} {x :: ys} {[]} {x₁ :: bs} record {} ys=bs = ys=bs
  appendWellDefined {S = S} {[]} {ys} {x :: as} {bs} () ys=bs
  appendWellDefined {S = S} {x :: xs} {ys} {[]} {bs} () ys=bs
  appendWellDefined {S = S} {x :: xs} {[]} {x₁ :: as} {[]} xs=as record {} = _&&_.fst xs=as ,, identityOfIndiscernablesRight (xs ++ []) (as) (as ++ []) (listEquality S) (identityOfIndiscernablesLeft xs as (xs ++ []) (listEquality S) (_&&_.snd xs=as) (equalityCommutative (appendEmptyList xs))) (equalityCommutative (appendEmptyList as))
  appendWellDefined {S = S} {x :: xs} {[]} {x₁ :: as} {x₂ :: bs} xs=as ()
  appendWellDefined {S = S} {x :: xs} {x₂ :: ys} {x₁ :: as} {[]} xs=as ()
  appendWellDefined {S = S} {x :: xs} {x₂ :: ys} {x₁ :: as} {x₃ :: bs} (fst ,, snd) ys=bs = fst ,, appendWellDefined snd ys=bs
