open import LogicalFormulae
open import Naturals

module Scratch where
  lem : {P Q : Set} → (P || (P → False)) → (P && Q → False) → Q → P
  lem {P} {Q} (inl x) pr q = exFalso (pr (record { fst = x ; snd = q }))
  lem {P} {Q} (inr notP) pr q = {!!}
