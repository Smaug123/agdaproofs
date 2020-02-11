{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Definition
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Fields.Fields
open import Rings.Orders.Total.Definition
open import Rings.Orders.Total.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Orders.LeastUpperBounds.Definition
open import Fields.Orders.Total.Definition
open import Sets.EquivalenceRelations

module Numbers.ClassicalReals.RealField.Lemmas {a b c : _} {A : Set a} {S : Setoid {_} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {pOrderedRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pOrderedRing) {orderNontrivialX orderNontrivialY : A} (orderNontrivial : orderNontrivialX < orderNontrivialY) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open SetoidPartialOrder pOrder
open import Rings.Orders.Partial.Lemmas pOrderedRing
open PartiallyOrderedRing pOrderedRing

IsOpenInterval : {d : _} {pred : A → Set d} (subset : subset S pred) → Set (a ⊔ c ⊔ d)
IsOpenInterval {pred = pred} subset = (x y : A) → (x<y : x < y) → pred x → pred y → (c : A) → (x < c) → (c < y) → pred c

nonemptyBoundedIntervalHasLubImpliesAllLub : ({d : _} {pred : A → Set d} {subset : subset S pred} (interval : IsOpenInterval subset) → (nonempty : Sg A pred) → (boundedAbove : Sg A (UpperBound pOrder subset)) → Sg A (LeastUpperBound pOrder subset)) → {d : _} → {pred : A → Set d} → (sub : subset S pred) → (nonempty : Sg A pred) → (boundedAbove : Sg A (UpperBound pOrder sub)) → Sg A (LeastUpperBound pOrder sub)
nonemptyBoundedIntervalHasLubImpliesAllLub axiom {d} {pred} sub (member , predMember) (bound , isBound) = lub , lubIsLub
  where
    intervalPredicate : A → Set (a ⊔ c ⊔ d)
    intervalPredicate a = Sg A (λ k → (a < k) && pred k)
    intervalIsSubset : subset S intervalPredicate
    intervalIsSubset {x} {y} x=y (bigger , (x<bigger ,, biggerWorks)) = (bigger , (<WellDefined x=y reflexive x<bigger ,, biggerWorks))
    intervalIsInterval : IsOpenInterval intervalIsSubset
    intervalIsInterval x y x<y (dominateX , (x<dominateX ,, predDominateX)) (dominateY , (y<dominateY ,, predDominateY)) c x<c c<y = dominateY , (<Transitive c<y y<dominateY ,, predDominateY)
    intervalNonempty : Sg A intervalPredicate
    intervalNonempty = ((member + orderNontrivialX) + inverse orderNontrivialY) , (member , (<WellDefined (transitive groupIsAbelian +Associative) identLeft (orderRespectsAddition (moveInequality' orderNontrivial) member) ,, predMember))
    intervalBounded : Sg A (UpperBound pOrder intervalIsSubset)
    intervalBounded = bound , ans
      where
        ans : (y : A) → intervalPredicate y → (y < bound) || (y ∼ bound)
        ans y (boundY , (y<boundY ,, predY)) with isBound boundY predY
        ans y (boundY , (y<boundY ,, predY)) | inl boundY<Bound = inl (<Transitive y<boundY boundY<Bound)
        ans y (boundY , (y<boundY ,, predY)) | inr boundY=Bound = inl (<WellDefined reflexive boundY=Bound y<boundY)
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
    ubImpliesUbSub {x} ub y (bound , (y<bound ,, predBound)) | inl bound<x = inl (<Transitive y<bound bound<x)
    ubImpliesUbSub {x} ub y (bound , (y<bound ,, predBound)) | inr bound=x = inl (<WellDefined reflexive bound=x y<bound)
    ubSubImpliesUb : {x : A} → UpperBound pOrder intervalIsSubset x → UpperBound pOrder sub x
    ubSubImpliesUb {x} ub y predY with ub y ({!!} , ({!!} ,, {!!}))
    ubSubImpliesUb {x} ub y predY | inl t<x = inl t<x
    ubSubImpliesUb {x} ub y predY | inr t=x = ?
    lubIsLub : LeastUpperBound pOrder sub lub
    LeastUpperBound.upperBound lubIsLub = ubSubImpliesUb (LeastUpperBound.upperBound lubProof)
    LeastUpperBound.leastUpperBound lubIsLub y yIsUpperBound = LeastUpperBound.leastUpperBound lubProof y (ubImpliesUbSub yIsUpperBound)
