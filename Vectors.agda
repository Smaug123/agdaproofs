{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Numbers.Naturals
open import Numbers.NaturalsWithK
open import Functions

data Vec {a : _} (X : Set a) : ℕ -> Set a where
  [] : Vec X zero
  _,-_ : {n : ℕ} -> X -> Vec X n -> Vec X (succ n)

vecLen : {a : _} {X : Set a} {n : ℕ} → Vec X n → ℕ
vecLen {a} {X} {n} v = n

vecHead : {a : _} {X : Set a} {n : ℕ} → Vec X (succ n) → X
vecHead (x ,- xs) = x

vecTail : {a : _} {X : Set a} {n : ℕ} → Vec X (succ n) → Vec X n
vecTail (x ,- xs) = xs

vecIsHeadPlusTail : {a : _} {X : Set a} {n : ℕ} → (xs : Vec X (succ n)) → (vecHead xs ,- vecTail xs) ≡ xs
vecIsHeadPlusTail (x ,- xs) = refl

_+V_ : {a : _} {X : Set a} {m n : ℕ} → Vec X m → Vec X n → Vec X (m +N n)
[] +V ys = ys
(x ,- xs) +V ys = (x ,- (xs +V ys))

vecIndex : {a : _} {X : Set a} {m : ℕ} → Vec X m → (i : ℕ) → (i <N m) → X
vecIndex [] zero (le x ())
vecIndex (x ,- vec) zero i<m = x
vecIndex [] (succ i) (le x ())
vecIndex (x ,- vec) (succ i) i<m = vecIndex vec i (canRemoveSuccFrom<N i<m)

vecLast : {a : _} {X : Set a} {m : ℕ} → Vec X m → (0 <N m) → X
vecLast {a} {X} {zero} v ()
vecLast {a} {X} {succ zero} (x ,- []) _ = x
vecLast {a} {X} {succ (succ m)} (x ,- v) _ = vecLast v (succIsPositive m)

vecAppend : {a : _} {X : Set a} {m : ℕ} → Vec X m → (x : X) → Vec X (succ m)
vecAppend {a} {X} {zero} [] x = x ,- []
vecAppend {a} {X} {succ m} (y ,- v) x = y ,- vecAppend v x

vecAppendIsNowLast : {a : _} {X : Set a} {m : ℕ} → (x : X) → (v : Vec X m) → (vecLast (vecAppend v x) (succIsPositive m)) ≡ x
vecAppendIsNowLast {a} {X} {zero} x [] = refl
vecAppendIsNowLast {a} {X} {succ m} x (y ,- v) = vecAppendIsNowLast x v

vecRev : {a : _} {X : Set a} {m : ℕ} → Vec X m → Vec X m
vecRev {a} {X} {zero} [] = []
vecRev {a} {X} {succ m} (x ,- v) = vecAppend (vecRev v) x

vecMoveAppend : {a : _} {X : Set a} {m : ℕ} → (x : X) → (v : Vec X m) → vecRev (vecAppend v x) ≡ x ,- vecRev v
vecMoveAppend {a} {X} {.0} x [] = refl
vecMoveAppend {a} {X} {.(succ _)} x (y ,- v) rewrite vecMoveAppend x v = refl

revRevIsId : {a : _} {X : Set a} {m : ℕ} → (v : Vec X m) → (vecRev (vecRev v)) ≡ v
revRevIsId {a} {X} {zero} [] = refl
revRevIsId {a} {X} {succ m} (x ,- v) rewrite vecMoveAppend x (vecRev v) = applyEquality (λ i → x ,- i) (revRevIsId v)

record vecContains {a : _} {X : Set a} {m : ℕ} (vec : Vec X m) (x : X) : Set a where
  field
    index : ℕ
    index<m : index <N m
    isHere : vecIndex vec index index<m ≡ x

vecSolelyContains : {a : _} {X : Set a} → {m : X} → (n : X) → (vecContains (m ,- []) n) → m ≡ n
vecSolelyContains {m} n record { index = zero ; index<m = _ ; isHere = isHere } = isHere
vecSolelyContains {m} n record { index = (succ index) ; index<m = (le x proof) ; isHere = isHere } = exFalso (f {x} {index} proof)
  where
    f : {x index : ℕ} → succ (x +N succ index) ≡ 1 → False
    f {x} {index} pr rewrite additionNIsCommutative x (succ index) = naughtE (equalityCommutative (succInjective pr))

vecChop : {a : _} {X : Set a} (m : ℕ) {n : ℕ} → Vec X (m +N n) → Vec X m && Vec X n
_&&_.fst (vecChop zero xs) = []
_&&_.fst (vecChop (succ m) (x ,- xs)) = (x ,- _&&_.fst (vecChop m xs))
_&&_.snd (vecChop zero xs) = xs
_&&_.snd (vecChop (succ m) (x ,- xs)) = _&&_.snd (vecChop m xs)

{-
vecIsChopThenAppend : {a : _} {X : Set a} {m n : ℕ} (xs : Vec X m) (ys : Vec X n) → vecChop m (xs +V ys) ≡ record { fst = xs ; snd = ys }
vecIsChopThenAppend {a} {X} {m} xs ys with vecChop m (xs +V ys)
vecIsChopThenAppend {a} {X} {zero} [] ys | record { fst = [] ; snd = snd } = {!!}
vecIsChopThenAppend {a} {X} {succ m} xs ys | bl = {!!}
-}

vecMap : {a b : _} {X : Set a} {Y : Set b} → (X → Y) → {n : ℕ} → Vec X n → Vec Y n
vecMap f [] = []
vecMap f (x ,- vec) = f x ,- (vecMap f vec)

vecMapCommutesWithAppend : {a b : _} {X : Set a} {Y : Set b} → (f : X → Y) → {n : ℕ} → (x : X) → (v : Vec X n) → (vecMap f (vecAppend v x) ≡ vecAppend (vecMap f v) (f x))
vecMapCommutesWithAppend f {.0} x [] = refl
vecMapCommutesWithAppend f {.(succ _)} x (y ,- v) = applyEquality (λ i → (f y ,- i)) (vecMapCommutesWithAppend f x v)

vecMapCommutesWithRev : {a b : _} {X : Set a} {Y : Set b} → (f : X → Y) → {n : ℕ} → (v : Vec X n) → (vecMap f (vecRev v) ≡ vecRev (vecMap f v))
vecMapCommutesWithRev {a} {b} {X} {Y} f {.0} [] = refl
vecMapCommutesWithRev {a} {b} {X} {Y} f {.(succ _)} (x ,- v) rewrite vecMapCommutesWithAppend f x (vecRev v) = applyEquality (λ i → vecAppend i (f x)) (vecMapCommutesWithRev f v)

vecIndex0AndAppend : {a : _} {X : Set a} {n : ℕ} → (v : Vec X n) → (0<n : 0 <N n) → (x : X) → vecIndex (vecAppend v x) 0 (succIsPositive n) ≡ vecIndex v 0 0<n
vecIndex0AndAppend [] () x
vecIndex0AndAppend (a ,- v) 0<n x = refl

vecIndexMAndAppend : {a : _} {X : Set a} {n : ℕ} → (v : Vec X n) → (x : X) → (m : ℕ) → (m<n : m <N n) → (pr : m <N succ n) → vecIndex (vecAppend v x) m pr ≡ vecIndex v m m<n
vecIndexMAndAppend {n = n} v x zero m<n pr rewrite <NRefl pr (succIsPositive n) = vecIndex0AndAppend v m<n x
vecIndexMAndAppend [] x (succ m) ()
vecIndexMAndAppend {n = n} (y ,- v) x (succ m) m<n pr = vecIndexMAndAppend v x m (canRemoveSuccFrom<N m<n) (canRemoveSuccFrom<N pr)

vecMapCompose : {a b c : _} {X : Set a} {Y : Set b} {Z : Set c} → (f : X → Y) → (g : Y → Z) → {n : ℕ} → (v : Vec X n) → (vecMap g (vecMap f v)) ≡ vecMap (λ i → g (f i)) v
vecMapCompose f g [] = refl
vecMapCompose f g (x ,- v) = applyEquality (λ w → (g (f x) ,- w)) (vecMapCompose f g v)

vecMapIdFact : {a : _} {X : Set a} {f : X → X} (feq : (x : X) → f x ≡ x) {n : ℕ} (xs : Vec X n) → vecMap f xs ≡ xs
vecMapIdFact feq [] = refl
vecMapIdFact feq (x ,- xs) rewrite (feq x) | vecMapIdFact feq xs = refl

vecMapCompositionFact : {a b c : _} {X : Set a} {Y : Set b} {Z : Set c} {f : Y → Z} {g : X → Y} {h : X → Z} (heq : (x : X) → f (g x) ≡ h x) → {n : ℕ} (xs : Vec X n) → vecMap f (vecMap g xs) ≡ vecMap h xs
vecMapCompositionFact heq [] = refl
vecMapCompositionFact {a} {b} {c} {X} {Y} {Z} {f} {g} {h} heq (x ,- xs) rewrite heq x | vecMapCompositionFact {a} {b} {c} {X} {Y} {Z} {f} {g} {h} heq xs = refl

vecMapIsNatural : {a b : _} {X : Set a} {Y : Set b} (f : X → Y) → {m n : ℕ} (xs : Vec X m) (xs' : Vec X n) → vecMap f (xs +V xs') ≡ (vecMap f xs +V vecMap f xs')
vecMapIsNatural f [] xs' = refl
vecMapIsNatural f (x ,- xs) xs' rewrite vecMapIsNatural f xs xs' = refl

vecPure : {a : _} {X : Set a} → X → {n : ℕ} → Vec X n
vecPure x {zero} = []
vecPure x {succ n} = x ,- vecPure x {n}

_$V_ : {a b : _} {X : Set a} {Y : Set b} {n : ℕ} → Vec (X → Y) n → Vec X n → Vec Y n
[] $V [] = []
(f ,- fs) $V (x ,- xs) = f x ,- (fs $V xs)
infixl 3 _$V_

vec : {a b : _} {X : Set a} {Y : Set b} → (X → Y) → {n : ℕ} → Vec X n → Vec Y n
vec f xs = (vecPure f) $V xs

vecZip : {a b : _} {X : Set a} {Y : Set b} {n : ℕ} → Vec X n → Vec Y n → Vec (X && Y) n
vecZip [] [] = []
vecZip (x ,- xs) (x₁ ,- ys) = record { fst = x ; snd = x₁ } ,- vecZip xs ys

vecIdentity : {a : _} {X : Set a} {f : X → X} (feq : (x : X) → f x ≡ x) → {n : ℕ} (xs : Vec X n) → (vecPure f $V xs) ≡ xs
vecIdentity feq [] = refl
vecIdentity feq (x ,- xs) rewrite feq x | vecIdentity feq xs = refl

vecHom : {a b : _} {X : Set a} {Y : Set b} (f : X → Y) (x : X) → {n : ℕ} → (vecPure f $V vecPure x) ≡ vecPure (f x) {n}
vecHom f x {zero} = refl
vecHom f x {succ n} rewrite vecHom f x {n} = refl

vecInterchange : {a b : _} {X : Set a} {Y : Set b} {n : ℕ} (fs : Vec (X → Y) n) (x : X) → (fs $V vecPure x) ≡ (vecPure (λ f → f x) $V fs)
vecInterchange [] x = refl
vecInterchange (f ,- fs) x rewrite vecInterchange fs x = refl

vecComposition : {a b c : _} {X : Set a} {Y : Set b} {Z : Set c} {n : ℕ} (fs : Vec (Y → Z) n) (gs : Vec (X → Y) n) (xs : Vec X n) → (vecPure (λ i j x → i (j x)) $V fs $V gs $V xs) ≡ (fs $V (gs $V xs))
vecComposition [] [] [] = refl
vecComposition (f ,- fs) (g ,- gs) (x ,- xs) rewrite vecComposition fs gs xs = refl

------------

data _<=_ : ℕ → ℕ → Set where
  oz : zero <= zero
  os : {n m : ℕ} → n <= m → succ n <= succ m
  o' : {n m : ℕ} → n <= m → n <= succ m

all0<=4 : Vec (0 <= 4) 1
all0<=4 = o' (o' (o' (o' oz))) ,- []

all1<=4 : Vec (1 <= 4) 4
all1<=4 = (o' ((o' (o' (os oz))))) ,- ((o' (o' (os (o' oz)))) ,- ((o' (os (o' (o' oz)))) ,- ((os (o' (o' (o' oz)))) ,- [])))

all2<=4 : Vec (2 <= 4) 6
all2<=4 = os (os (o' (o' oz))) ,- (os (o' (os (o' oz))) ,- (os (o' (o' (os oz))) ,- (o' (o' (os (os oz))) ,- (o' (os (o' (os oz))) ,- (o' (os (os (o' oz))) ,- [])))))

all3<=4 : Vec (3 <= 4) 4
all3<=4 = os (os (os (o' oz))) ,- (os (os (o' (os oz))) ,- (os (o' (os (os oz))) ,- (o' (os (os (os oz))) ,- [])))

all4<=4 : Vec (4 <= 4) 1
all4<=4 = os (os (os (os oz))) ,- []

<=Is≤N : {n m : ℕ} → (n <= m) → n ≤N m
<=Is≤N {n} {m} thm with orderIsTotal n m
<=Is≤N {n} {m} thm | inl (inl n<m) = inl n<m
<=Is≤N {n} {.n} thm | inr refl = inr refl
<=Is≤N {zero} {zero} thm | inl (inr m<n) = inl m<n
<=Is≤N {zero} {succ m} thm | inl (inr m<n) = inl (succIsPositive m)
<=Is≤N {succ n} {zero} () | inl (inr m<n)
<=Is≤N {succ n} {succ m} (os thm) | inl (inr m<n) with <=Is≤N thm
<=Is≤N {succ n} {succ m} (os thm) | inl (inr m<n) | inl x = inl (succPreservesInequality x)
<=Is≤N {succ n} {succ m} (os thm) | inl (inr m<n) | inr x rewrite x = inr refl
<=Is≤N {succ n} {succ m} (o' thm) | inl (inr m<n) with <=Is≤N thm
<=Is≤N {succ n} {succ m} (o' thm) | inl (inr m<n) | inl x with a<SuccA m
... | m<sm = inl (lessTransitive x m<sm)
<=Is≤N {succ n} {succ m} (o' thm) | inl (inr m<n) | inr x rewrite x = inl (a<SuccA m)

succIsNotEqual : {n : ℕ} → (succ n ≡ n) → False
succIsNotEqual {zero} pr = naughtE (equalityCommutative pr)
succIsNotEqual {succ n} pr = succIsNotEqual (succInjective pr)

succIsNotLess : {n : ℕ} → (succ n <N n) → False
succIsNotLess {zero} (le x proof) = naughtE (equalityCommutative proof)
succIsNotLess {succ n} pr = succIsNotLess (canRemoveSuccFrom<N pr)

noSN<=N : {n : ℕ} → (succ n) <= n → False
noSN<=N {n} thm with <=Is≤N thm
noSN<=N {n} thm | inl x = succIsNotLess x
noSN<=N {n} thm | inr x = succIsNotEqual x

no5<=4 : 5 <= 4 → False
no5<=4 th = noSN<=N {4} th

_<?=_ : {a : _} {X : Set a} {n m : ℕ} → (n <= m) → Vec X m → Vec X n
oz <?= xs = xs
os th <?= (x ,- xs) = x ,- (th <?= xs)
o' th <?= (x ,- xs) = th <?= xs

vMap<?=Fact : {a b : _} {X : Set a} {Y : Set b} (f : X → Y) {n m : ℕ} (th : n <= m) (xs : Vec X m) → vecMap f (th <?= xs) ≡ (th <?= vecMap f xs)
vMap<?=Fact f oz xs = refl
vMap<?=Fact f (os th) (x ,- xs) rewrite vMap<?=Fact f th xs = refl
vMap<?=Fact f (o' th) (x ,- xs) rewrite vMap<?=Fact f th xs = refl

oi : {n : ℕ} → n <= n
oi {zero} = oz
oi {succ n} = os oi

oe : {n : ℕ} → 0 <= n
oe {zero} = oz
oe {succ n} = o' oe

oeUnique : {n : ℕ} (th : 0 <= n) → th ≡ oe
oeUnique oz = refl
oeUnique (o' i) rewrite oeUnique i = refl

oTooBig : {n m : ℕ} → m ≤N n → succ n <= m → False
oTooBig {n} {m} m<=n th with <=Is≤N th
oTooBig {n} {m} (inl m<n) th | inl x = succIsNotLess (lessTransitive x m<n)
oTooBig {n} {m} (inr m=n) th | inl x rewrite m=n = succIsNotLess x
oTooBig {n} {m} (inl m<n) th | inr x rewrite (equalityCommutative x) = succIsNotLess m<n
oTooBig {n} {m} (inr m=n) th | inr x rewrite m=n = succIsNotEqual x

oiUnique : {n : ℕ} (th : n <= n) → (th ≡ oi)
oiUnique oz = refl
oiUnique (os th) rewrite oiUnique th = refl
oiUnique {succ n} (o' th) with oTooBig {n} {n} (inr refl) th
... | bl = exFalso bl

id-<?= : {a : _} {X : Set a} {n : ℕ} (xs : Vec X n) → (oi <?= xs) ≡ xs
id-<?= [] = refl
id-<?= (x ,- xs) rewrite id-<?= xs = refl

_o>>_ : {p n m : ℕ} → p <= n → n <= m → p <= m
oz o>> th' = th'
os th o>> os th' = os (th o>> th')
os th o>> o' th' = os (o' th o>> th')
o' th o>> os th' = o' (th o>> th')
o' th o>> o' th' = o' (o' th o>> th')

eqHelper : {a : _} {X : Set a} (x : X) {n : ℕ} {r s : Vec X n} (pr : r ≡ s) → (x ,- r) ≡ (x ,- s)
eqHelper x pr rewrite pr = refl
