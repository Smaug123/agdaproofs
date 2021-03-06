{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Monoids.Definition

module Semirings.Definition where

record Semiring {a : _} {A : Set a} (Zero One : A) (_+_ : A → A → A) (_*_ : A → A → A) : Set a where
  field
    monoid : Monoid Zero _+_
    commutative : (a b : A) → a + b ≡ b + a
    multMonoid : Monoid One _*_
    productZeroLeft : (a : A) → Zero * a ≡ Zero
    productZeroRight : (a : A) → a * Zero ≡ Zero
    +DistributesOver* : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    +DistributesOver*' : (a b c : A) → (a + b) * c ≡ (a * c) + (b * c)
  +Associative = Monoid.associative monoid
  *Associative = Monoid.associative multMonoid
  productOneLeft = Monoid.idLeft multMonoid
  productOneRight = Monoid.idRight multMonoid
  sumZeroLeft = Monoid.idLeft monoid
  sumZeroRight = Monoid.idRight monoid
  +WellDefined : {a b c d : A} → (a ≡ c) → (b ≡ d) → (a + b) ≡ (c + d)
  +WellDefined refl refl = refl

-- (b+c)(a+a) == b(a+a) + c(a+a) == ba+ba+ca+ca == (ba+ca) + (ba+ca)
-- (b+c)(a+a) ==? (b+c)a+(b+c)a
