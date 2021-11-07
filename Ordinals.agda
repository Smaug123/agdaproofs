{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Orders.WellFounded.Definition
open import Orders.WellFounded.Induction
open import Orders.Partial.Definition
open import Orders.Total.Definition
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Ordinals where

record Ordinal {a b : _} : Set (lsuc a ⊔ lsuc b) where
  field
    A : Set a
    _<_ : Rel {a} {b} A
    wf : WellFounded _<_

succSet : {a b : _} → (o : Ordinal {a} {b}) → Set a
succSet o = True || Ordinal.A o

succComp : {a b : _} → (o : Ordinal {a} {b}) → Rel (succSet o)
succComp o (inl record {}) y = False'
succComp o (inr x) (inl record {}) = True'
succComp o (inr x) (inr y) = Ordinal._<_ o x y

private
  lemma' : {a b : _} → {o : Ordinal {a} {b}} → (x : Ordinal.A o) → Accessible (Ordinal._<_ o) x → Accessible (succComp o) (inr x)
  lemma' {o = o} = rec (Ordinal.wf o) _ ans
    where
      open Ordinal o
      ans : (x : A) → ((y : A) → y < x → Accessible _<_ y → Accessible (succComp o) (inr y)) → Accessible _<_ x → Accessible (succComp o) (inr x)
      ans x induction (access f) = access u
        where
          u : (y : succSet o) → succComp o y (inr x) → Accessible (succComp o) y
          u (inr y) y<x = induction y y<x (f y y<x)

  lemma : {a b : _} → {o : Ordinal {a} {b}} → (x : Ordinal.A o) → Accessible (succComp o) (inr x)
  lemma {o = o} x with Ordinal.wf o x
  ... | access f = access t
    where
      t : (y : succSet o) → succComp o y (inr x) → Accessible (succComp o) y
      t (inr y) y<x with f y y<x
      ... | u = lemma' _ u

succWf : {a b : _} → (o : Ordinal {a} {b}) → WellFounded (succComp o)
succWf o (inl record {}) = access t
  where
    t : (y : succSet o) → succComp o y (inl (record {})) → Accessible (succComp o) y
    t (inr x) record {} = lemma x
succWf o (inr x) = access t
  where
    t : (y : succSet o) → succComp o y (inr x) → Accessible (succComp o) y
    t (inr y) y<x = lemma y

succ : {a b : _} → Ordinal {a} {b} → Ordinal
succ o = record { A = succSet o ; _<_ = succComp o ; wf = succWf o }

OrdinalIsomorphism : {a b c d : _} {o1 : Ordinal {a} {b}} {o2 : Ordinal {c} {d}} → {f : Ordinal.A o1 → Ordinal.A o2} → Bijection f → Set (a ⊔ b ⊔ d)
OrdinalIsomorphism {o1 = o1} {o2 = o2} {f = f} bij = (x y : Ordinal.A o1) → Ordinal._<_ o1 x y → Ordinal._<_ o2 (f x) (f y)

wellOrderIsTotal : {a b : _} {A : Set a} {_<_ : Rel {a} {b} A} → WellFounded _<_ → TotalOrder A {b}
PartialOrder._<_ (TotalOrder.order (wellOrderIsTotal {_<_ = _<_} wf)) = _<_
PartialOrder.irreflexive (TotalOrder.order (wellOrderIsTotal {A = A} {_<_ = _<_} wf)) {x} = ans x
  where
    ans : (x : A) → ((x < x) → False)
    ans = rec wf (λ z → (x : z < z) → False) λ i pr i<i → pr i i<i i<i
PartialOrder.<Transitive (TotalOrder.order (wellOrderIsTotal {A = A} {_<_ = _<_} wf)) {a} {b} {c} = ans b
  where
    pr : (x : A) → ((y : A) → y < x → a < y → y < c → a < c) → a < x → x < c → a < c
    pr x induction a<x x<c with wf x
    ... | access xAc = induction {!!} {!!} {!!} {!!}
    ans : (b : A) → (a < b) → (b < c) → a < c
    ans = rec wf _ pr
TotalOrder.totality (wellOrderIsTotal {A = A} {_<_ = _<_} wf) a b = {!!}
  where
    pr : (x : A) → ((y : A) → y < x → ((y < b) || (b < y)) || (y ≡ b)) → ((x < b) || (b < x)) || (x ≡ b)
    pr x induction with wf x
    pr x induction | access x₁ = {!!}
    ans : (a : A) → ((a < b) || (b < a)) || (a ≡ b)
    ans = rec wf _ pr

record OrdinalsIsomorphic {a b c d : _} (o1 : Ordinal {a} {b}) (o2 : Ordinal {c} {d}) : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    f : Ordinal.A o1 → Ordinal.A o2
    bij : Bijection f
    isIso : OrdinalIsomorphism {o1 = o1} {o2 = o2} {f = f} bij

isoImpliesUniqueIso : {a b c d : _} {o1 : Ordinal {a} {b}} {o2 : Ordinal {c} {d}} → (iso1 iso2 : OrdinalsIsomorphic o1 o2) → (x : Ordinal.A o1) → OrdinalsIsomorphic.f iso1 x ≡ OrdinalsIsomorphic.f iso2 x
isoImpliesUniqueIso {o1 = o1} record { f = f1 ; bij = bij1 ; isIso = isIso1 } record { f = f2 ; bij = bij2 ; isIso = isIso2 } = rec (Ordinal.wf o1) _ ans
  where
    ans : (x : Ordinal.A o1) → ((y : Ordinal.A o1) → (Ordinal._<_ o1) y x → f1 y ≡ f2 y) → f1 x ≡ f2 x
    ans x induction = {!!}

succNotIsomorphic : {a b : _} → (o : Ordinal {a} {b}) → OrdinalsIsomorphic o (succ o) → False
succNotIsomorphic o record { f = f ; bij = bij ; isIso = isIso } = {!!}
