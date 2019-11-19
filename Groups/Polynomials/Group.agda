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
open import Vectors
open import Lists.Lists
open import Maybe

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Polynomials.Group {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Groups.Polynomials.Definition G
open import Groups.Polynomials.Addition G public
open Setoid S
open Equivalence eq

polyGroup : Group naivePolySetoid _+P_
Group.+WellDefined polyGroup = +PwellDefined
Group.0G polyGroup = []
Group.inverse polyGroup = inverse'
Group.+Associative polyGroup {a} {b} {c} = assoc {a} {b} {c}
Group.identRight polyGroup = PidentRight
Group.identLeft polyGroup = PidentLeft
Group.invLeft polyGroup {a} = invLeft' {a}
Group.invRight polyGroup {a} = invRight' {a}

abelian : AbelianGroup G → AbelianGroup polyGroup
AbelianGroup.commutative (abelian ab) {x} {y} = comm ab {x} {y}
