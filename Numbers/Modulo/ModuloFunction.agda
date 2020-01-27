{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.EuclideanAlgorithm
open import Semirings.Definition
open import Orders.Total.Definition

module Numbers.Modulo.ModuloFunction where

open TotalOrder ℕTotalOrder

private
  notBigger : (a : ℕ) {n : ℕ} → succ a +N n ≡ a → False
  notBigger (succ a) {n} pr = notBigger a {n} (succInjective pr)

  notBigger' : (a : ℕ) {n : ℕ} → succ a +N n ≡ n → False
  notBigger' (succ a) {succ n} pr rewrite Semiring.commutative ℕSemiring a (succ n) | Semiring.commutative ℕSemiring n a = notBigger' _ (succInjective pr)

abstract
  mod : (n : ℕ) → .(pr : 0 <N n) → (a : ℕ) → ℕ
  mod (succ n) 0<n a = divisionAlgResult.rem (divisionAlg (succ n) a)

  modIsMod : {n : ℕ} → .(pr : 0 <N n) → (a : ℕ) → a <N n → mod n pr a ≡ a
  modIsMod {succ n} 0<n a a<n with divisionAlg (succ n) a
  modIsMod {succ n} 0<n a a<n | record { quot = zero ; rem = rem ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } rewrite multiplicationNIsCommutative n 0 = pr
  modIsMod {succ n} 0<n a (le x proof) | record { quot = succ quot ; rem = rem ; pr = pr ; remIsSmall = inl rem<sn ; quotSmall = quotSmall } = exFalso (notBigger a v)
    where
      t : ((succ (a +N x)) *N succ quot) +N rem ≡ a
      t rewrite Semiring.commutative ℕSemiring a x = transitivity (applyEquality (λ i → (i *N succ quot) +N rem) proof) pr
      u : (succ quot *N succ (a +N x)) +N rem ≡ a
      u = transitivity (applyEquality (_+N rem) (multiplicationNIsCommutative (succ quot) _)) t
      v : succ a +N ((x +N quot *N succ (a +N x)) +N rem) ≡ a
      v = transitivity (applyEquality succ (transitivity (Semiring.+Associative ℕSemiring a _ rem) (applyEquality (_+N rem) (Semiring.+Associative ℕSemiring a x _)))) u

  mod<N : {n : ℕ} → .(pr : 0 <N n) → (a : ℕ) → (mod n pr a) <N n
  mod<N {succ n} pr a with divisionAlg (succ n) a
  mod<N {succ n} 0<n a | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl x ; quotSmall = quotSmall } = x

  modIdempotent : {n : ℕ} → .(pr : 0 <N n) → (a : ℕ) → mod n pr (mod n pr a) ≡ mod n pr a
  modIdempotent 0<n a = modIsMod 0<n (mod _ 0<n a) (mod<N 0<n a)

  modAnd+n : {n : ℕ} → .(pr : 0 <N n) → (a : ℕ) → mod n pr (n +N a) ≡ mod n pr a
  modAnd+n {succ n} 0<sn a with divisionAlg (succ n) (succ n +N a)
  modAnd+n {succ n} 0<sn a | record { quot = 0 ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = inl q } rewrite multiplicationNIsCommutative n 0 | pr = exFalso (notBigger (succ n) (transitivity (applyEquality succ (transitivity (applyEquality succ (Semiring.+Associative ℕSemiring n a _)) (Semiring.commutative ℕSemiring (succ (n +N a)) _))) (_<N_.proof remIsSmall)))
  modAnd+n {succ n} 0<sn a | record { quot = succ quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = inl q } = modIsUnique (record { quot = quot ; rem = rem ; pr = t ; remIsSmall = inl remIsSmall ; quotSmall = inl q }) (divisionAlg (succ n) a)
    where
      g : succ n +N ((quot *N succ n) +N rem) ≡ succ n +N a
      g = transitivity (Semiring.+Associative ℕSemiring (succ n) _ rem) (transitivity (applyEquality (_+N rem) (multiplicationNIsCommutative (succ quot) _)) pr)
      h : (quot *N succ n) +N rem ≡ a
      h = canSubtractFromEqualityLeft g
      t : (succ n *N quot) +N rem ≡ a
      t = transitivity (applyEquality (_+N rem) (multiplicationNIsCommutative (succ n) quot)) h

  modExtracts : {n : ℕ} → .(pr : 0 <N n) → (a b : ℕ) → mod n pr (a +N b) ≡ mod n pr (mod n pr a +N mod n pr b)
  modExtracts {succ n} 0<sn a b with divisionAlg (succ n) a
  modExtracts {succ n} 0<sn a b | record { quot = sn/a ; rem = sn%a ; pr = prA ; remIsSmall = remIsSmallA ; quotSmall = quotSmallA } with divisionAlg (succ n) b
  modExtracts {succ n} 0<sn a b | record { quot = sn/a ; rem = sn%a ; pr = prA ; remIsSmall = remIsSmallA ; quotSmall = quotSmallA } | record { quot = sn/b ; rem = sn%b ; pr = prB ; remIsSmall = remIsSmallB ; quotSmall = quotSmallB } with divisionAlg (succ n) (a +N b)
  modExtracts {succ n} 0<sn a b | record { quot = sn/a ; rem = sn%a ; pr = prA ; remIsSmall = remIsSmallA ; quotSmall = quotSmallA } | record { quot = sn/b ; rem = sn%b ; pr = prB ; remIsSmall = remIsSmallB ; quotSmall = quotSmallB } | record { quot = sn/a+b ; rem = sn%a+b ; pr = prA+B ; remIsSmall = remIsSmallA+B ; quotSmall = quotSmallA+B } with divisionAlg (succ n) (sn%a +N sn%b)
  modExtracts {succ n} 0<sn a b | record { quot = sn/a ; rem = sn%a ; pr = prA ; remIsSmall = inl sn%a<sn ; quotSmall = inl _ } | record { quot = sn/b ; rem = sn%b ; pr = prB ; remIsSmall = inl sn%b<sn ; quotSmall = inl _ } | record { quot = sn/a+b ; rem = sn%a+b ; pr = prA+B ; remIsSmall = inl sn%a+b<sn ; quotSmall = inl _ } | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = inl _ } = equalityCommutative whoa
    where
      t : ((succ n *N sn/a) +N sn%a) +N ((succ n *N sn/b) +N sn%b) ≡ a +N b
      t = +NWellDefined prA prB
      t' : (succ n *N (sn/a +N sn/b)) +N (sn%a +N sn%b) ≡ a +N b
      t' = transitivity (transitivity (Semiring.+Associative ℕSemiring (succ n *N (sn/a +N sn/b)) sn%a sn%b) (transitivity (applyEquality (_+N sn%b) (transitivity (transitivity (applyEquality (_+N sn%a) (transitivity (applyEquality (succ n *N_) (Semiring.commutative ℕSemiring sn/a sn/b)) (Semiring.+DistributesOver* ℕSemiring (succ n) sn/b sn/a))) (equalityCommutative (Semiring.+Associative ℕSemiring (succ n *N sn/b) (succ n *N sn/a) sn%a))) (Semiring.commutative ℕSemiring (succ n *N sn/b) ((succ n *N sn/a) +N sn%a)))) (equalityCommutative (Semiring.+Associative ℕSemiring ((succ n *N sn/a) +N sn%a) (succ n *N sn/b) sn%b)))) t
      thing : ((succ n) *N quot) +N rem ≡ sn%a +N sn%b
      thing = pr
      t'' : (succ n *N ((sn/a +N sn/b) +N quot)) +N rem ≡ a +N b
      t'' rewrite Semiring.+DistributesOver* ℕSemiring (succ n) (sn/a +N sn/b) quot | equalityCommutative (Semiring.+Associative ℕSemiring (succ n *N (sn/a +N sn/b)) (succ n *N quot) rem) | thing = t'
      whoa : rem ≡ sn%a+b
      whoa = modUniqueLemma _ _ remIsSmall sn%a+b<sn (transitivity t'' (equalityCommutative prA+B))

  modAddition : {n : ℕ} → .(pr : 0 <N n) → {a b : ℕ} → (a <N n) → (b <N n) → (a +N b ≡ mod n pr (a +N b)) || (a +N b ≡ n +N mod n pr (a +N b))
  modAddition {succ n} 0<sn {a} {b} a<n b<n with divisionAlg (succ n) (a +N b)
  modAddition {succ n} 0<sn {a} {b} a<n b<n | record { quot = zero ; rem = rem ; pr = pr ; remIsSmall = inl rem<sn ; quotSmall = inl _ } = inl (equalityCommutative (transitivity (applyEquality (_+N rem) (multiplicationNIsCommutative 0 n)) pr))
  modAddition {succ n} 0<sn {a} {b} a<n b<n | record { quot = succ zero ; rem = rem ; pr = pr ; remIsSmall = inl rem<sn ; quotSmall = inl _ } = inr (transitivity (equalityCommutative pr) (applyEquality (λ i → succ i +N rem) (transitivity (multiplicationNIsCommutative n 1) (Semiring.sumZeroRight ℕSemiring n))))
  modAddition {succ n} 0<sn {a} {b} (le x prA) (le y prB) | record { quot = succ (succ quot) ; rem = 0 ; pr = pr ; remIsSmall = inl rem<sn ; quotSmall = inl _ } rewrite Semiring.sumZeroRight ℕSemiring (succ n *N succ (succ quot)) | multiplicationNIsCommutative (succ n) (succ (succ quot)) = exFalso (notBigger' ((x +N succ y) +N (quot *N succ n)) u)
    where
      t : ((succ x +N a) +N succ (y +N b)) +N (quot *N succ n) ≡ a +N b
      t = transitivity (transitivity (applyEquality (_+N quot *N succ n) (+NWellDefined prA prB)) (equalityCommutative (Semiring.+Associative ℕSemiring (succ n) (succ n) (quot *N succ n)))) pr
      u : ((succ x +N succ y) +N (quot *N succ n)) +N (a +N b) ≡ a +N b
      u rewrite Semiring.commutative ℕSemiring ((x +N succ y) +N quot *N succ n) (a +N b) | Semiring.+Associative ℕSemiring (succ a +N b) (x +N succ y) (quot *N succ n) = transitivity (applyEquality (λ i → succ i +N quot *N succ n) (transitivity (Semiring.commutative ℕSemiring (a +N b) _) (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring x (succ y) _)) (transitivity (applyEquality (x +N_) (transitivity (Semiring.+Associative ℕSemiring (succ y) a b) (transitivity (applyEquality (_+N b) (Semiring.commutative ℕSemiring _ a)) (equalityCommutative (Semiring.+Associative ℕSemiring a (succ y) b))))) (Semiring.+Associative ℕSemiring x a _))))) t
  modAddition {succ n} 0<sn {a} {b} a<n b<n | record { quot = succ (succ quot) ; rem = succ rem ; pr = pr ; remIsSmall = inl rem<sn ; quotSmall = inl _ } = exFalso (irreflexive (<Transitive u t))
    where
      t : (succ n *N succ (succ quot) +N succ rem) <N succ n +N succ n
      t = identityOfIndiscernablesLeft _<N_ (addStrongInequalities a<n b<n) (equalityCommutative pr)
      lemm : {a c d : ℕ} → (a +N a) <N (a *N succ (succ c)) +N succ d
      lemm {a} {c} {d} = le (a *N c +N d) f
        where
          f : succ ((a *N c +N d) +N (a +N a)) ≡ a *N succ (succ c) +N succ d
          f rewrite multiplicationNIsCommutative a (succ (succ c)) | Semiring.+Associative ℕSemiring a a (c *N a) | multiplicationNIsCommutative c a | Semiring.commutative ℕSemiring (a *N c +N d) (a +N a) | Semiring.+Associative ℕSemiring (a +N a) (a *N c) d | Semiring.commutative ℕSemiring ((a +N a) +N a *N c) (succ d) = applyEquality succ (Semiring.commutative ℕSemiring _ d)
      u : (succ n +N succ n) <N (succ n *N succ (succ quot) +N succ rem)
      u = lemm {succ n}

  modN : {n : ℕ} → .(0<n : 0 <N n) → mod n 0<n n ≡ 0
  modN {succ n} 0<n = modIsUnique (divisionAlg (succ n) (succ n)) record { quot = 1 ; rem = zero ; pr = ans ; remIsSmall = inl (le n (Semiring.sumZeroRight ℕSemiring (succ n))) ; quotSmall = inl (le n (Semiring.sumZeroRight ℕSemiring (succ n))) }
    where
      ans : succ (n *N 1 +N 0) ≡ succ n
      ans rewrite multiplicationNIsCommutative n 1 | Semiring.sumZeroRight ℕSemiring n | Semiring.sumZeroRight ℕSemiring n = refl
