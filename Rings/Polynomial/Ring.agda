{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Abelian.Definition
open import Groups.Homomorphisms.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Lists.Lists
open import Rings.Homomorphisms.Definition


module Rings.Polynomial.Ring {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open Setoid S
open Equivalence eq
open import Groups.Polynomials.Group additiveGroup
open import Groups.Polynomials.Definition additiveGroup
open import Rings.Polynomial.Multiplication R

polyRing : Ring naivePolySetoid _+P_ _*P_
Ring.additiveGroup polyRing = polyGroup
Ring.*WellDefined polyRing {a} {b} {c} {d} = *PwellDefined {a} {b} {c} {d}
Ring.1R polyRing = 1R :: []
Ring.groupIsAbelian polyRing {x} {y} = AbelianGroup.commutative (abelian (record { commutative = Ring.groupIsAbelian R })) {x} {y}
Ring.*Associative polyRing {a} {b} {c} = *Passoc {a} {b} {c}
Ring.*Commutative polyRing {a} {b} = p*Commutative {a} {b}
Ring.*DistributesOver+ polyRing {a} {b} {c} = *Pdistrib {a} {b} {c}
Ring.identIsIdent polyRing {a} = *Pident {a}

polyInjectionIsHom : RingHom R polyRing polyInjection
RingHom.preserves1 polyInjectionIsHom = reflexive ,, record {}
RingHom.ringHom polyInjectionIsHom = reflexive ,, (reflexive ,, record {})
GroupHom.groupHom (RingHom.groupHom polyInjectionIsHom) = reflexive ,, record {}
GroupHom.wellDefined (RingHom.groupHom polyInjectionIsHom) = SetoidInjection.wellDefined polyInjectionIsInj
