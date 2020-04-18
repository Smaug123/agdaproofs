{-# OPTIONS --safe --warning=error --without-K #-}

open import Boolean.Definition
open import Sets.FinSet.Definition
open import LogicalFormulae
open import Groups.Abelian.Definition
open import Groups.Vector
open import Groups.Definition
open import Groups.Abelian.Definition
open import Numbers.Integers.Integers
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Modules.Definition
open import Groups.Cyclic.Definition
open import Groups.Cyclic.DefinitionLemmas
open import Rings.Polynomial.Multiplication
open import Rings.Polynomial.Ring
open import Rings.Definition
open import Rings.Lemmas
open import Groups.Polynomials.Definition
open import Numbers.Naturals.Semiring
open import Vectors
open import Modules.Span
open import Numbers.Integers.Definition
open import Numbers.Integers.Addition
open import Rings.IntegralDomains.Definition
open import Numbers.Naturals.Order
open import Numbers.Modulo.Definition
open import Numbers.Modulo.Group

module Modules.Examples where

abGrpModule : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {G' : Group S _+_} (G : AbelianGroup G') → Module ℤRing G (λ x i → elementPower G' i x)
Module.dotWellDefined (abGrpModule {S = S} {G' = G'} G) {m} {n} {g} {h} m=n g=h = transitive (elementPowerWellDefinedG G' g h g=h {m}) (elementPowerWellDefinedZ' G' m n m=n {h})
  where
    open Setoid S
    open Equivalence eq
Module.dotDistributesLeft (abGrpModule {G' = G'} G) {n} {x} {y} = elementPowerHomAbelian G' (AbelianGroup.commutative G) x y n
Module.dotDistributesRight (abGrpModule {S = S} {G' = G'} G) {r} {s} {x} = symmetric (elementPowerCollapse G' x r s)
  where
    open Equivalence (Setoid.eq S)
Module.dotAssociative (abGrpModule {G' = G'} G) {r} {s} {x} = elementPowerMultiplies G' r s x
Module.dotIdentity (abGrpModule {G' = G'} G) = Group.identRight G'

zAndZ : Module ℤRing ℤAbGrp _*Z_
Module.dotWellDefined zAndZ refl refl = refl
Module.dotDistributesLeft zAndZ = Ring.*DistributesOver+ ℤRing
Module.dotDistributesRight zAndZ {x} {y} {z} = Ring.*DistributesOver+' ℤRing {x} {y} {z}
Module.dotAssociative zAndZ {x} {y} {z} = equalityCommutative (Ring.*Associative ℤRing {x} {y} {z})
Module.dotIdentity zAndZ = Ring.identIsIdent ℤRing

twoOrAnother : ℤ → Bool → ℤ
twoOrAnother _ BoolTrue = nonneg 2
twoOrAnother n BoolFalse = n

23Spans : Spans zAndZ (twoOrAnother (nonneg 3))
23Spans m = 2 , (((BoolTrue ,- (BoolFalse ,- [])) ,, (Group.inverse ℤGroup m ,- (m ,- []))) , t m)
  where
    open Group ℤGroup
    open Ring ℤRing
    t : (m : ℤ) → inverse m *Z nonneg 2 +Z (m *Z nonneg 3 +Z nonneg 0) ≡ m
    t m rewrite identRight {m *Z nonneg 3} | *DistributesOver+ {m} {nonneg 2} {nonneg 1} | +Associative {inverse m *Z nonneg 2} {m *Z nonneg 2} {m *Z nonneg 1} = transitivity (transitivity (+WellDefined {inverse m *Z nonneg 2 +Z m *Z nonneg 2} {m *Z nonneg 1} {nonneg 0} {_} (transitivity (equalityCommutative (*DistributesOver+' {inverse m} {m} {nonneg 2})) (*WellDefined (invLeft {m}) refl)) refl) *Commutative) identIsIdent

evenNotOdd : (i : ℤ) → nonneg 0 ≡ i *Z nonneg 2 +Z nonneg 1 → False
evenNotOdd (nonneg x) pr rewrite equalityCommutative (+Zinherits (x *N 2) 1) = evenNotOdd' x (nonnegInjective pr)
  where
    evenNotOdd' : (i : ℕ) → 0 ≡ i *N 2 +N 1 → False
    evenNotOdd' zero ()
    evenNotOdd' (succ i) ()
evenNotOdd (negSucc zero) ()
evenNotOdd (negSucc (succ zero)) ()
evenNotOdd (negSucc (succ (succ x))) ()

2NotSpan : Spans zAndZ {_} {True} (λ _ → nonneg 2) → False
2NotSpan f with f (nonneg 1)
2NotSpan f | n , (trues , b) = bad (_&&_.fst trues) (_&&_.snd trues) (nonneg 0) b
  where
    open Group ℤGroup
    open Ring ℤRing
    bad : {n : ℕ} → (t : Vec True n) (u : Vec ℤ n) (i : ℤ) → dot zAndZ (vecMap (λ _ → nonneg 2) t) u ≡ ((i *Z nonneg 2) +Z nonneg 1) → False
    bad [] [] i x = evenNotOdd i x
    bad (record {} ,- t) (u ,- us) i x = bad t us (i +Z inverse u) (transitivity (+WellDefined (equalityCommutative (invLeft {u *Z nonneg 2})) refl) (transitivity (equalityCommutative (+Associative {inverse (u *Z nonneg 2)} {u *Z nonneg 2})) (transitivity (+WellDefined (refl {x = inverse (u *Z nonneg 2)}) x) (transitivity (+Associative {inverse (u *Z nonneg 2)} {i *Z nonneg 2}) (+WellDefined {inverse (u *Z nonneg 2) +Z i *Z nonneg 2} {_} {(i +Z inverse u) *Z nonneg 2} (transitivity (transitivity (groupIsAbelian {inverse (u *Z nonneg 2)}) (applyEquality (i *Z nonneg 2 +Z_) (equalityCommutative (ringMinusExtracts' ℤRing)))) (equalityCommutative (*DistributesOver+' {i} {inverse u} {nonneg 2}))) (refl {x = nonneg 1}))))))

3NotSpan : Spans zAndZ {_} {True} (λ _ → nonneg 3) → False
3NotSpan f with f (nonneg 1)
... | n , ((trues ,, coeffs) , b) = bad trues coeffs (nonneg 0) b
  where
    open Group ℤGroup
    open Ring ℤRing
    bad : {n : ℕ} → (t : Vec True n) (u : Vec ℤ n) (i : ℤ) → dot zAndZ (vecMap (λ _ → nonneg 3) t) u ≡ ((i *Z nonneg 3) +Z nonneg 1) → False
    bad [] [] (nonneg zero) ()
    bad [] [] (nonneg (succ i)) ()
    bad [] [] (negSucc zero) ()
    bad [] [] (negSucc (succ i)) ()
    bad (record {} ,- ts) (u ,- us) i x = bad ts us (i +Z inverse u) (transitivity (+WellDefined (equalityCommutative (invLeft {u *Z nonneg 3})) (refl {x = dot zAndZ (vecMap (λ _ → nonneg 3) ts) us})) (transitivity (equalityCommutative (+Associative {inverse (u *Z nonneg 3)} {u *Z nonneg 3})) (transitivity (+WellDefined (equalityCommutative (ringMinusExtracts' ℤRing {u} {nonneg 3})) x) (transitivity (+Associative {inverse u *Z nonneg 3} {i *Z nonneg 3} {nonneg 1}) (+WellDefined (transitivity {x = (inverse u *Z nonneg 3 +Z i *Z nonneg 3)} (equalityCommutative (*DistributesOver+' {inverse u} {i})) (*WellDefined (groupIsAbelian {inverse u} {i}) (refl {x = nonneg 3}))) (refl {x = nonneg 1}))))))

nothingNotSpan : Spans zAndZ {_} {False} (λ ()) → False
nothingNotSpan f with f (nonneg 1)
nothingNotSpan f | zero , (([] ,, []) , ())
nothingNotSpan f | succ n , (((() ,- fst) ,, snd) , b)

1Basis : Basis zAndZ {_} {True} (λ _ → nonneg 1)
_&&_.fst 1Basis m = 1 , (((record {} ,- []) ,, (m ,- [])) , transitivity (Group.+WellDefined ℤGroup (transitivity (Ring.*Commutative ℤRing {m}) (Ring.identIsIdent ℤRing)) refl) (Group.identRight ℤGroup))
_&&_.snd 1Basis {zero} r x [] x₁ = record {}
_&&_.snd 1Basis {succ zero} (record {} ,- []) x (b ,- []) pr = equalityCommutative (transitivity (equalityCommutative (transitivity (Group.+WellDefined ℤGroup (transitivity (Ring.*Commutative ℤRing {b}) (Ring.identIsIdent ℤRing)) refl) (Group.identRight ℤGroup))) pr) ,, record {}
_&&_.snd 1Basis {succ (succ n)} (record {} ,- (record {} ,- r)) x b pr with x {0} {1} (succIsPositive _) (succPreservesInequality (succIsPositive _)) refl
_&&_.snd 1Basis {succ (succ n)} (record {} ,- (record {} ,- r)) x b pr | ()

2Independent : Independent zAndZ {_} {True} (λ _ → nonneg 2)
2Independent {zero} r x [] x₁ = record {}
2Independent {succ zero} (record {} ,- []) x (coeff ,- []) pr rewrite Group.identRight ℤGroup {coeff *Z nonneg 2} = equalityCommutative (IntegralDomain.intDom ℤIntDom (transitivity (Ring.*Commutative ℤRing) pr) λ ()) ,, record {}
2Independent {succ (succ n)} (record {} ,- (record {} ,- rest)) pr b x = exFalso (naughtE t)
  where
    t : 0 ≡ 1
    t = pr {0} {1} (succIsPositive (succ n)) (succPreservesInequality (succIsPositive n)) refl

2AndExtraNotIndependent : (n : ℤ) → Independent zAndZ (twoOrAnother n) → False
2AndExtraNotIndependent n indep = exFalso (naughtE (nonnegInjective ohNo))
  where
    r : {a b : ℕ} → (a<n : a <N 2) → (b<n : b <N 2) → vecIndex (BoolTrue ,- (BoolFalse ,- [])) a a<n ≡ vecIndex (BoolTrue ,- (BoolFalse ,- [])) b b<n → a ≡ b
    r {zero} {zero} a<n b<n x = refl
    r {zero} {succ (succ b)} a<n (le (succ zero) ()) x
    r {zero} {succ (succ b)} a<n (le (succ (succ y)) ()) x
    r {succ zero} {succ zero} a<n b<n x = refl
    r {succ zero} {succ (succ b)} a<n (le (succ zero) ()) x
    r {succ zero} {succ (succ b)} a<n (le (succ (succ i)) ()) x
    r {succ (succ a)} {b} (le (succ zero) ()) b<n x
    r {succ (succ a)} {b} (le (succ (succ i)) ()) b<n x
    s : dot zAndZ (vecMap (twoOrAnother n) (BoolTrue ,- (BoolFalse ,- []))) (Group.inverse ℤGroup n ,- (nonneg 2 ,- [])) ≡ nonneg 0
    s rewrite Group.identRight ℤGroup {nonneg 2 *Z n} | Ring.*Commutative ℤRing {nonneg 2} {n} | equalityCommutative (Ring.*DistributesOver+' ℤRing {additiveInverse n} {n} {nonneg 2}) | Group.invLeft ℤGroup {n} = refl
    t : _=V_ zAndZ (Ring.additiveGroup ℤRing) (nonneg 0 ,- (nonneg 0 ,- [])) (Group.inverse ℤGroup n ,- (nonneg 2 ,- []))
    t = indep (BoolTrue ,- (BoolFalse ,- [])) r (Group.inverse ℤGroup n ,- (nonneg 2 ,- [])) s

    ohNo : nonneg 0 ≡ nonneg 2
    ohNo with t
    ohNo | ()

oneLengthAlwaysInj : {a b : ℕ} → (a<n : a <N 1) → (b<n : b <N 1) → a ≡ b
oneLengthAlwaysInj {zero} {zero} a<n b<n = refl
oneLengthAlwaysInj {zero} {succ b} a<n (le zero ())
oneLengthAlwaysInj {zero} {succ b} a<n (le (succ x) ())
oneLengthAlwaysInj {succ a} {b} (le zero ()) b<n
oneLengthAlwaysInj {succ a} {b} (le (succ x) ()) b<n

noBasisExample : Independent (abGrpModule (ℤnAbGroup 5 (le 4 refl))) (λ (t : True) → record { x = 1 ; xLess = le 3 refl }) → False
noBasisExample ind with ind (record {} ,- []) (λ a<n b<n _ → oneLengthAlwaysInj a<n b<n) (nonneg 5 ,- []) refl
noBasisExample ind | ()
