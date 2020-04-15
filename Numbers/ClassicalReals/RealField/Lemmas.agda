{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders.Partial.Definition
open import Fields.Fields
open import Rings.Orders.Total.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Orders.LeastUpperBounds.Definition
open import Fields.Orders.Total.Definition
open import Sets.EquivalenceRelations

module Numbers.ClassicalReals.RealField.Lemmas {a b c : _} {A : Set a} {S : Setoid {_} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} (pOrderedRing : PartiallyOrderedRing R pOrder) {orderNontrivialX orderNontrivialY : A} (orderNontrivial : orderNontrivialX < orderNontrivialY) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open SetoidPartialOrder pOrder
open import Rings.Orders.Partial.Lemmas pOrderedRing
open PartiallyOrderedRing pOrderedRing

IsInterval : {d : _} {pred : A → Set d} (subset : subset S pred) → Set (a ⊔ c ⊔ d)
IsInterval {pred = pred} subset = (x y : A) → (x<y : x < y) → pred x → pred y → (c : A) → (x < c) → (c < y) → pred c

-- Example: (a, b) is an interval
openBallPred : A → A → A → Set c
openBallPred a b x = (a < x) && (x < b)
openBallSubset : (a b : A) → subset S (openBallPred a b)
openBallSubset a b {x} {y} x=y (a<x ,, x<y) = <WellDefined reflexive x=y a<x ,, <WellDefined x=y reflexive x<y
openBallInterval : (a b : A) → IsInterval (openBallSubset a b)
openBallInterval a b x y x<y (a<x ,, x<b) (a<y ,, y<b) c x<c c<y = <Transitive a<x x<c ,, <Transitive c<y y<b

nonemptyBoundedIntervalHasLubImpliesAllLub : ({d : _} {pred : A → Set d} {subset : subset S pred} (interval : IsInterval subset) → (nonempty : Sg A pred) → (boundedAbove : Sg A (UpperBound pOrder subset)) → Sg A (LeastUpperBound pOrder subset)) → {d : _} → {pred : A → Set d} → (sub : subset S pred) → (nonempty : Sg A pred) → (boundedAbove : Sg A (UpperBound pOrder sub)) → Sg A (LeastUpperBound pOrder sub)
nonemptyBoundedIntervalHasLubImpliesAllLub axiom {d} {pred} sub (member , predMember) (bound , isBound) = lub , lubIsLub
  where
    intervalPredicate : A → Set (a ⊔ b ⊔ c ⊔ d)
    intervalPredicate a = Sg A (λ k → ((a < k) || (a ∼ k)) && pred k)
    intervalIsSubset : subset S intervalPredicate
    intervalIsSubset {x} {y} x=y (bigger , (inl x<bigger ,, biggerWorks)) = (bigger , (inl (<WellDefined x=y reflexive x<bigger) ,, biggerWorks))
    intervalIsSubset {x} {y} x=y (bigger , (inr x=bigger ,, biggerWorks)) = (bigger , (inr (transitive (symmetric x=y) x=bigger) ,, biggerWorks))
    intervalIsInterval : IsInterval intervalIsSubset
    intervalIsInterval x y x<y (dominateX , (x<dominateX ,, predDominateX)) (dominateY , (inl y<dominateY ,, predDominateY)) c x<c c<y = dominateY , (inl (<Transitive c<y y<dominateY) ,, predDominateY)
    intervalIsInterval x y x<y (dominateX , (x<dominateX ,, predDominateX)) (dominateY , (inr y=dominateY ,, predDominateY)) c x<c c<y = dominateY , (inl (<WellDefined reflexive y=dominateY c<y) ,, predDominateY)
    intervalNonempty : Sg A intervalPredicate
    intervalNonempty = ((member + orderNontrivialX) + inverse orderNontrivialY) , (member , (inl (<WellDefined (transitive groupIsAbelian +Associative) identLeft (orderRespectsAddition (moveInequality' orderNontrivial) member)) ,, predMember))
    intervalBounded : Sg A (UpperBound pOrder intervalIsSubset)
    intervalBounded = bound , ans
      where
        ans : (y : A) → intervalPredicate y → (y < bound) || (y ∼ bound)
        ans y (boundY , (y<boundY ,, predY)) with isBound boundY predY
        ans y (boundY , (inl y<boundY ,, predY)) | inl boundY<Bound = inl (<Transitive y<boundY boundY<Bound)
        ans y (boundY , (inr y=boundY ,, predY)) | inl boundY<Bound = inl (<WellDefined (symmetric y=boundY) reflexive boundY<Bound)
        ans y (boundY , (inl y<boundY ,, predY)) | inr boundY=Bound = inl (<WellDefined reflexive boundY=Bound y<boundY)
        ans y (boundY , (inr y=boundY ,, predY)) | inr boundY=Bound = inr (transitive y=boundY boundY=Bound)
    intervalLub : Sg A (LeastUpperBound pOrder intervalIsSubset)
    intervalLub = axiom intervalIsInterval intervalNonempty intervalBounded
    lub : A
    lub with intervalLub
    ... | b , _ = b
    lubProof : LeastUpperBound pOrder intervalIsSubset lub
    lubProof with intervalLub
    ... | b , pr = pr
    ubImpliesUbSub : {x : A} → UpperBound pOrder sub x → UpperBound pOrder intervalIsSubset x
    ubImpliesUbSub {x} ub y (bound , (y<bound ,, predBound)) with ub bound predBound
    ubImpliesUbSub {x} ub y (bound , (inl y<bound ,, predBound)) | inl bound<x = inl (<Transitive y<bound bound<x)
    ubImpliesUbSub {x} ub y (bound , (inr y=bound ,, predBound)) | inl bound<x = inl (<WellDefined (symmetric y=bound) reflexive bound<x)
    ubImpliesUbSub {x} ub y (bound , (inl y<bound ,, predBound)) | inr bound=x = inl (<WellDefined reflexive bound=x y<bound)
    ubImpliesUbSub {x} ub y (bound , (inr y=bound ,, predBound)) | inr bound=x = inr (transitive y=bound bound=x)
    ubSubImpliesUb : {x : A} → UpperBound pOrder intervalIsSubset x → UpperBound pOrder sub x
    ubSubImpliesUb {x} ub y predY with ub y (y , (inr reflexive ,, predY))
    ubSubImpliesUb {x} ub y predY | inl t<x = inl t<x
    ubSubImpliesUb {x} ub y predY | inr t=x = inr t=x
    lubIsLub : LeastUpperBound pOrder sub lub
    LeastUpperBound.upperBound lubIsLub = ubSubImpliesUb (LeastUpperBound.upperBound lubProof)
    LeastUpperBound.leastUpperBound lubIsLub y yIsUpperBound = LeastUpperBound.leastUpperBound lubProof y (ubImpliesUbSub yIsUpperBound)
