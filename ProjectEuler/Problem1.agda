{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Lists.Lists
open import Numbers.Primes.PrimeNumbers
open import Decidable.Relations
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Addition

module ProjectEuler.Problem1 where

numbers<N : (N : ℕ) → List ℕ
numbers<N zero = []
numbers<N (succ N) = N :: numbers<N N

filtered : (N : ℕ) → List ℕ
filtered N = filter' (orDecidable (divisionDecidable 3) (divisionDecidable 5)) (numbers<N N)

ans : ℕ → ℕ
ans n = binNatToN (fold _+B_ (NToBinNat 0) (map NToBinNat (filtered n)))

t : ans 10 ≡ 23
t = refl

--q : ans 1000 ≡ 0 -- takes about 15secs for me to reduce the term that fills this hole
--q = refl
