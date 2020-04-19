{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Groups.Definition

module Groups.Subgroups.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Setoids.Subset S
open Group G

record Subgroup {c : _} (pred : A → Set c) : Set (a ⊔ b ⊔ c) where
  field
    isSubset : subset pred
    closedUnderPlus : {g h : A} → (pred g) → (pred h) → pred (g + h)
    containsIdentity : pred 0G
    closedUnderInverse : ({g : A} → (pred g) → (pred (inverse g)))

subgroupOp : {c : _} {pred : A → Set c} → (s : Subgroup pred) → Sg A pred → Sg A pred → Sg A pred
subgroupOp {pred = pred} record { closedUnderPlus = one } (a , prA) (b , prB) = (a + b) , one prA prB

subgroupIsGroup : {c : _} {pred : A → Set c} → (s : Subgroup pred) → Group (subsetSetoid (Subgroup.isSubset s)) (subgroupOp s)
Group.+WellDefined (subgroupIsGroup s) {m , prM} {n , prN} {x , prX} {y , prY} m=x n=y = +WellDefined m=x n=y
Group.0G (subgroupIsGroup record { containsIdentity = two }) = 0G , two
Group.inverse (subgroupIsGroup record { closedUnderInverse = three }) (a , prA) = (inverse a) , three prA
Group.+Associative (subgroupIsGroup s) {a , prA} {b , prB} {c , prC} = +Associative
Group.identRight (subgroupIsGroup s) {a , prA} = identRight
Group.identLeft (subgroupIsGroup s) {a , prA} = identLeft
Group.invLeft (subgroupIsGroup s) {a , prA} = invLeft
Group.invRight (subgroupIsGroup s) {a , prA} = invRight
