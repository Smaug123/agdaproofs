{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Groups.Homomorphisms.Definition

module Groups.Subgroups.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) where

open import Setoids.Subset S
open Group G

subgroup : {c : _} (pred : A → Set c) → Set (a ⊔ b ⊔ c)
subgroup pred = subset pred && (({g h : A} → (pred g) → (pred h) → pred (g + h)) & pred 0G & ({g : A} → (pred g) → (pred (inverse g))))

subgroupOp : {c : _} {pred : A → Set c} → (s : subgroup pred) → Sg A pred → Sg A pred → Sg A pred
subgroupOp {pred = pred} (_ ,, record { one = one ; two = two ; three = three }) (a , prA) (b , prB) = (a + b) , one prA prB

subgroupIsGroup : {c : _} {pred : A → Set c} → (subs : subset pred) → (s : subgroup pred) → Group (subsetSetoid subs) (subgroupOp s)
Group.+WellDefined (subgroupIsGroup _ s) {m , prM} {n , prN} {x , prX} {y , prY} m=x n=y = +WellDefined m=x n=y
Group.0G (subgroupIsGroup _ (_ ,, record { two = two })) = 0G , two
Group.inverse (subgroupIsGroup _ (_ ,, record { three = three })) (a , prA) = (inverse a) , three prA
Group.+Associative (subgroupIsGroup _ s) {a , prA} {b , prB} {c , prC} = +Associative
Group.identRight (subgroupIsGroup _ s) {a , prA} = identRight
Group.identLeft (subgroupIsGroup _ s) {a , prA} = identLeft
Group.invLeft (subgroupIsGroup _ s) {a , prA} = invLeft
Group.invRight (subgroupIsGroup _ s) {a , prA} = invRight
