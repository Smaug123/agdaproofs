{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.DirectSum.Definition
open import Setoids.Setoids
open import Rings.Definition


module Rings.DirectSum {a b c d : _} {A : Set a} {S : Setoid {a} {b} A} {_+1_ : A → A → A} {_*1_ : A → A → A} {C : Set c} {T : Setoid {c} {d} C} {_+2_ : C → C → C} {_*2_ : C → C → C} (R1 : Ring S _+1_ _*1_) (R2 : Ring T _+2_ _*2_) where

open import Setoids.DirectSum S T

pairPlus : A && C → A && C → A && C
pairPlus (a ,, b) (c ,, d) = (a +1 c) ,, (b +2 d)

pairTimes : A && C → A && C → A && C
pairTimes (a ,, b) (c ,, d) = (a *1 c) ,, (b *2 d)

directSumRing : Ring directSumSetoid pairPlus pairTimes
Ring.additiveGroup directSumRing = directSumGroup (Ring.additiveGroup R1) (Ring.additiveGroup R2)
Ring.*WellDefined directSumRing r=t s=u = directSumLift (Ring.*WellDefined R1 (_&&_.fst r=t) (_&&_.fst s=u)) (Ring.*WellDefined R2 (_&&_.snd r=t) (_&&_.snd s=u))
Ring.1R directSumRing = Ring.1R R1 ,, Ring.1R R2
Ring.groupIsAbelian directSumRing = directSumLift (Ring.groupIsAbelian R1) (Ring.groupIsAbelian R2)
Ring.*Associative directSumRing = directSumLift (Ring.*Associative R1) (Ring.*Associative R2)
Ring.*Commutative directSumRing = directSumLift (Ring.*Commutative R1) (Ring.*Commutative R2)
Ring.*DistributesOver+ directSumRing = directSumLift (Ring.*DistributesOver+ R1) (Ring.*DistributesOver+ R2)
Ring.identIsIdent directSumRing = directSumLift (Ring.identIsIdent R1) (Ring.identIsIdent R2)
