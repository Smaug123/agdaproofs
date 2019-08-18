{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Functions
open import Groups.Groups
open import Groups.GroupDefinition
open import Orders
open import Rings.Definition
open import Numbers.Naturals
open import Numbers.Integers
open import PrimeNumbers
open import IntegersModN

module Rings.Examples.Proofs where
  nToZn' : (n : ℕ) (pr : 0 <N n) (x : ℕ) → ℤn n pr
  nToZn' 0 ()
  nToZn' (succ n) pr x with divisionAlg (succ n) x
  nToZn' (succ n) pr1 x | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl thing ; quotSmall = quotSmall } = record { x = rem ; xLess = thing }
  nToZn' (succ n) pr1 x | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }

  mod' : (n : ℕ) → (pr : 0 <N n) → ℤ → ℤn n pr
  mod' zero () a
  mod' (succ n) pr (nonneg x) = nToZn' (succ n) pr x
  mod' (succ n) pr (negSucc x) = Group.inverse (ℤnGroup (succ n) pr) (nToZn' (succ n) pr (succ x))

  subtractionEquiv : (a : ℕ) → {b c : ℕ} → (c<b : c <N b) → a +N c ≡ b → a ≡ subtractionNResult.result (-N (inl c<b))
  subtractionEquiv 0 {b} {c} c<b pr rewrite pr = exFalso (PartialOrder.irreflexive (TotalOrder.order ℕTotalOrder) c<b)
  subtractionEquiv (succ a) {b} {c} c<b pr = equivalentSubtraction 0 b (succ a) c (succIsPositive a) c<b (equalityCommutative pr)

  modNExampleSurjective' : (n : ℕ) → (pr : 0 <N n) → Surjection (mod' n pr)
  Surjection.property (modNExampleSurjective' zero ())
  Surjection.property (modNExampleSurjective' (succ n) pr) record { x = x ; xLess = xLess } with divisionAlg (succ n) x
  Surjection.property (modNExampleSurjective' (succ n) p) record { x = x ; xLess = xLess } | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = q } = nonneg x , lhs'
    where
      rs' : rem ≡ x
      rs' = modIsUnique (record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = q }) (record { quot = 0 ; rem = x ; pr = blah ; remIsSmall = inl xLess ; quotSmall = inl (succIsPositive n) })
        where
          blah : n *N 0 +N x ≡ x
          blah rewrite multiplicationNIsCommutative n 0 = refl
      lhs : nToZn' (succ n) p x ≡ record { x = rem ; xLess = remIsSmall }
      lhs with divisionAlg (succ n) x
      lhs | record { quot = quot' ; rem = rem' ; pr = pr' ; remIsSmall = inl t ; quotSmall = quotSmall } = equalityZn _ _ (equalityCommutative rs)
        where
          rs : rem ≡ rem'
          rs = modIsUnique (record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall; quotSmall = q }) (record { quot = quot' ; rem = rem' ; pr = pr' ; remIsSmall = inl t ; quotSmall = quotSmall })
      lhs | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }
      lhs' : nToZn' (succ n) p x ≡ record { x = x ; xLess = xLess }
      lhs' = transitivity lhs (equalityZn _ _ rs')
  Surjection.property (modNExampleSurjective' (succ n) p) record { x = x ; xLess = xLess } | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }

{-
  modNExampleGroupHom' : (n : ℕ) → (pr : 0 <N n) → GroupHom ℤGroup (ℤnGroup n pr) (mod' n pr)
  modNExampleGroupHom' 0 ()
  GroupHom.wellDefined (modNExampleGroupHom' (succ n) pr) {x} {.x} refl = refl
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {nonneg a} {nonneg b} with divisionAlg (succ n) a
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {nonneg a} {nonneg b} | record { quot = quotA ; rem = remA ; pr = prA ; remIsSmall = inl remA<sn ; quotSmall = quotSmallA } with divisionAlg (succ n) b
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {nonneg a} {nonneg b} | record { quot = quotA ; rem = remA ; pr = prA ; remIsSmall = inl remA<sn ; quotSmall = quotSmallA } | record { quot = quotB ; rem = remB ; pr = prB ; remIsSmall = inl remB<sn ; quotSmall = quotSmallB } with orderIsTotal (remA +N remB) (succ n)
  GroupHom.groupHom (modNExampleGroupHom' (succ n) pr1) {nonneg a} {nonneg b} | record { quot = quotA ; rem = remA ; pr = prA ; remIsSmall = inl remA<sn ; quotSmall = _ } | record { quot = quotB ; rem = remB ; pr = prB ; remIsSmall = inl remB<sn ; quotSmall = _ } | inl (inl rarb<sn) rewrite addingNonnegIsHom a b = equalityZn _ _ lemma
    where
      lemma : ℤn.x (nToZn' (succ n) pr1 (a +N b)) ≡ remA +N remB
      lemma with divisionAlg (succ n) (a +N b)
      lemma | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl x ; quotSmall = inl _ } = equalityCommutative thing5
        where
          thing : ((succ n) *N quotA +N remA) +N ((succ n) *N quotB +N remB) ≡ a +N b
          thing rewrite prA | prB = refl
          thing2 : ((succ n) *N quotA +N remA) +N ((succ n) *N quotB +N remB) ≡ (succ n) *N quot +N rem
          thing2 rewrite pr = thing
          thing3 : (((succ n) *N quotA) +N ((succ n) *N quotB)) +N (remA +N remB) ≡ (succ n) *N quot +N rem
          thing3 rewrite equalityCommutative (additionNIsAssociative (((succ n) *N quotA) +N ((succ n) *N quotB)) remA remB) | additionNIsAssociative ((succ n) *N quotA) ((succ n) *N quotB) remA | additionNIsCommutative ((succ n) *N quotB) remA | equalityCommutative (additionNIsAssociative ((succ n) *N quotA) remA ((succ n) *N quotB)) | additionNIsAssociative ((succ n) *N quotA +N remA) ((succ n) *N quotB) remB = thing2
          thing4 : (succ n) *N (quotA +N quotB) +N (remA +N remB) ≡ (succ n) *N quot +N rem
          thing4 rewrite productDistributes (succ n) quotA quotB = thing3
          thing5 : remA +N remB ≡ rem
          thing5 = modUniqueLemma {remA +N remB} {rem} {succ n} (quotA +N quotB) quot rarb<sn x thing4
      lemma | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl x ; quotSmall = inr () }
      lemma | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }
  GroupHom.groupHom (modNExampleGroupHom' (succ n) pr1) {nonneg a} {nonneg b} | record { quot = quotA ; rem = remA ; pr = prA ; remIsSmall = inl remA<sn } | record { quot = quotB ; rem = remB ; pr = prB ; remIsSmall = inl remB<sn } | inl (inr sn<rarb) rewrite addingNonnegIsHom a b = equalityZn _ _ lemma
    where
      lemma : ℤn.x (nToZn' (succ n) pr1 (a +N b)) ≡ subtractionNResult.result (-N (inl sn<rarb))
      lemma with divisionAlg (succ n) (a +N b)
      lemma | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl x ; quotSmall = q } = modIsUnique record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl x ; quotSmall = q } record { quot = succ quotA +N quotB ; rem = subtractionNResult.result (-N (inl sn<rarb)) ; pr = answer ; remIsSmall = inl remSmall ; quotSmall = inl (succIsPositive n) }
        where
          transform : (a : ℕ) → {b c : ℕ} → (p : b <N c) → c <N a +N b → subtractionNResult.result (-N (inl p)) <N a
          transform a {b} {c} pr (le y proof1) with addIntoSubtraction (succ y) {b} {c} (inl pr)
          ... | bl = le y (transitivity bl (equalityCommutative (subtractionEquiv a (orderIsTransitive pr (addingIncreases c y)) (equalityCommutative (identityOfIndiscernablesLeft _ _ _ _≡_ proof1 (additionNIsCommutative (succ y) c))))))
          thing : ((succ n) *N quotA +N remA) +N ((succ n) *N quotB +N remB) ≡ a +N b
          thing rewrite prA | prB = refl
          thing2 : (((succ n) *N quotA) +N ((succ n) *N quotB)) +N (remA +N remB) ≡ a +N b
          thing2 = identityOfIndiscernablesLeft _ _ _ _≡_ thing (transitivity (equalityCommutative (additionNIsAssociative ((quotA +N n *N quotA) +N remA) (succ n *N quotB) remB)) (transitivity (applyEquality (λ i → i +N remB) (additionNIsAssociative (quotA +N n *N quotA) remA (quotB +N n *N quotB))) (transitivity (applyEquality (λ i → ((quotA +N n *N quotA) +N i) +N remB) (additionNIsCommutative remA (quotB +N n *N quotB))) (transitivity (applyEquality (λ i → i +N remB) (equalityCommutative (additionNIsAssociative (quotA +N n *N quotA) (quotB +N n *N quotB) remA))) (additionNIsAssociative _ remA remB)))))
          thing3 : (succ n) *N (quotA +N quotB) +N (remA +N remB) ≡ a +N b
          thing3 = identityOfIndiscernablesLeft _ _ _ _≡_ thing2 (equalityCommutative (applyEquality (λ i → i +N (remA +N remB)) (productDistributes (succ n) (quotA) quotB)))
          answer : (succ n *N succ (quotA +N quotB)) +N subtractionNResult.result (-N (inl sn<rarb)) ≡ a +N b
          answer with addIntoSubtraction (succ n *N succ (quotA +N quotB)) (inl sn<rarb)
          ... | bl = transitivity bl (moveOneSubtraction' {a<=b = inl (orderIsTransitive sn<rarb (addingIncreases (remA +N remB) ((quotA +N quotB) +N n *N succ (quotA +N quotB))))} answer')
            where
              snTimes1 : succ n ≡ succ n *N 1
              snTimes1 rewrite multiplicationNIsCommutative (succ n) 1 | additionNIsCommutative (succ n) 0 = refl
              q' : succ n *N succ (quotA +N quotB) ≡ succ n +N (succ n *N (quotA +N quotB))
              q' rewrite additionNIsCommutative (succ n) (succ n *N (quotA +N quotB)) | snTimes1 | equalityCommutative (productDistributes (succ n) (quotA +N quotB) 1) = applyEquality (λ i → (succ n) *N i) (succIsAddOne (quotA +N quotB))
              answer'' : (succ n *N succ (quotA +N quotB)) +N (remA +N remB) ≡ (succ n) +N ((succ n *N (quotA +N quotB)) +N (remA +N remB))
              answer'' rewrite equalityCommutative (additionNIsAssociative (succ n) (succ n *N (quotA +N quotB)) (remA +N remB)) = applyEquality (λ i → i +N (remA +N remB)) q'
              answer' : (remA +N remB) +N (succ n *N succ (quotA +N quotB)) ≡ succ n +N (a +N b)
              answer' rewrite equalityCommutative thing3 = transitivity (additionNIsCommutative (remA +N remB) (succ n *N succ (quotA +N quotB))) answer''
          remSmall : subtractionNResult.result (-N (inl sn<rarb)) <N succ n
          remSmall = transform (succ n) sn<rarb (addStrongInequalities remA<sn remB<sn)
      lemma | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }
  GroupHom.groupHom (modNExampleGroupHom' (succ n) pr1) {nonneg a} {nonneg b} | record { quot = quotA ; rem = remA ; pr = prA ; remIsSmall = inl remA<sn } | record { quot = quotB ; rem = remB ; pr = prB ; remIsSmall = inl remB<sn } | inr rarb=sn rewrite addingNonnegIsHom a b = equalityZn _ _ lemma
    where
      lemma : ℤn.x (nToZn' (succ n) pr1 (a +N b)) ≡ 0
      lemma with divisionAlg (succ n) (a +N b)
      lemma | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl x } = equalityCommutative (modUniqueLemma ((quotA +N quotB) +N 1) quot pr1 x thing7)
        where
          thing : ((succ n) *N quotA +N remA) +N ((succ n) *N quotB +N remB) ≡ a +N b
          thing rewrite prA | prB = refl
          thing2 : ((succ n) *N quotA +N remA) +N ((succ n) *N quotB +N remB) ≡ (succ n) *N quot +N rem
          thing2 rewrite pr = thing
          thing3 : (((succ n) *N quotA) +N ((succ n) *N quotB)) +N (remA +N remB) ≡ (succ n) *N quot +N rem
          thing3 rewrite equalityCommutative (additionNIsAssociative (((succ n) *N quotA) +N ((succ n) *N quotB)) remA remB) | additionNIsAssociative ((succ n) *N quotA) ((succ n) *N quotB) remA | additionNIsCommutative ((succ n) *N quotB) remA | equalityCommutative (additionNIsAssociative ((succ n) *N quotA) remA ((succ n) *N quotB)) | additionNIsAssociative ((succ n) *N quotA +N remA) ((succ n) *N quotB) remB = thing2
          thing4 : (succ n) *N (quotA +N quotB) +N (remA +N remB) ≡ (succ n) *N quot +N rem
          thing4 rewrite productDistributes (succ n) quotA quotB = thing3
          thing5 : (succ n) *N (quotA +N quotB) +N (succ n) ≡ (succ n) *N quot +N rem
          thing5 rewrite equalityCommutative rarb=sn = thing4
          thing6 : (succ n) *N ((quotA +N quotB) +N 1) ≡ (succ n) *N quot +N rem
          thing6 rewrite productDistributes (succ n) (quotA +N quotB) 1 | multiplicationNIsCommutative n 1 | additionNIsCommutative n 0 = thing5
          thing7 : (succ n) *N ((quotA +N quotB) +N 1) +N 0 ≡ (succ n) *N quot +N rem
          thing7 = identityOfIndiscernablesLeft _ _ _ _≡_ thing6 (additionNIsCommutative 0 _)
      lemma | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {nonneg a} {nonneg b} | record { quot = quotA ; rem = remA ; pr = prA ; remIsSmall = inl remA<sn ; quotSmall = quotSmallA } | record { quot = quotB ; rem = remB ; pr = prB ; remIsSmall = inr () ; quotSmall = quotSmallB }
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {nonneg a} {nonneg b} | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () ; quotSmall = quotSmall }
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {nonneg a} {negSucc b} with divisionAlg (succ n) a
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {nonneg a} {negSucc b} | record { quot = quotA ; rem = remA ; pr = prA ; remIsSmall = remIsSmallA ; quotSmall = quotSmallA } = {!!}
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {negSucc x} {nonneg b} with divisionAlg (succ n) (succ x)
  ... | bl = {!!}
  GroupHom.groupHom (modNExampleGroupHom' (succ n) _) {negSucc x} {negSucc b} with divisionAlg (succ n) (succ x)
  ... | bl = {!!}

-}
