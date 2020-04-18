{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Functions.Definition

module Sets.EquivalenceRelations where

Reflexive : {a b : _} {A : Set a} (r : Rel {a} {b} A) → Set (a ⊔ b)
Reflexive {A = A} r = {x : A} → r x x

Symmetric : {a b : _} {A : Set a} (r : Rel {a} {b} A) → Set (a ⊔ b)
Symmetric {A = A} r = {x y : A} → r x y → r y x

Transitive : {a b : _} {A : Set a} (r : Rel {a} {b} A) → Set (a ⊔ b)
Transitive {A = A} r = {x y z : A} → r x y → r y z → r x z

record Equivalence {a b : _} {A : Set a} (r : Rel {a} {b} A) : Set (a ⊔ lsuc b) where
  field
    reflexive : Reflexive r
    symmetric : Symmetric r
    transitive : Transitive r
    -- See https://lists.chalmers.se/pipermail/agda/2016/009090.html
  transitive' : {x y z : A} → r y z → r x y → r x z
  transitive' p2 p1 = transitive p1 p2
