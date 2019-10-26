{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations

module Groups.Groups where

reflGroupWellDefined : {lvl : _} {A : Set lvl} {m n x y : A} {op : A → A → A} → m ≡ x → n ≡ y → (op m n) ≡ (op x y)
reflGroupWellDefined {lvl} {A} {m} {n} {.m} {.n} {op} refl refl = refl

record AbelianGroup {a} {b} {A : Set a} {S : Setoid {a} {b} A} {_·_ : A → A → A} (G : Group S _·_) : Set (lsuc a ⊔ b) where
  open Setoid S
  field
    commutative : {a b : A} → (a · b) ∼ (b · a)

groupsHaveLeftCancellation : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → (x y z : A) → (Setoid._∼_ S (x · y) (x · z)) → (Setoid._∼_ S y z)
groupsHaveLeftCancellation {_·_ = _·_} {S} g x y z pr = o
  where
  open Group g renaming (inverse to _^-1)
  open Setoid S
  transitive = Equivalence.transitive (Setoid.eq S)
  symmetric = Equivalence.symmetric (Setoid.eq S)
  j : ((x ^-1) · x) · y ∼ (x ^-1) · (x · z)
  j = Equivalence.transitive eq (symmetric (+Associative {x ^-1} {x} {y})) (+WellDefined ~refl pr)
  k : ((x ^-1) · x) · y ∼ ((x ^-1) · x) · z
  k = transitive j +Associative
  l : 0G · y ∼ ((x ^-1) · x) · z
  l = transitive (+WellDefined (symmetric invLeft) ~refl) k
  m : 0G · y ∼ 0G · z
  m = transitive l (+WellDefined invLeft ~refl)
  n : y ∼ 0G · z
  n = transitive (symmetric identLeft) m
  o : y ∼ z
  o = transitive n identLeft

groupsHaveRightCancellation : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → (x y z : A) → (Setoid._∼_ S (y · x) (z · x)) → (Setoid._∼_ S y z)
groupsHaveRightCancellation {_·_ = _·_} {S} g x y z pr = transitive m identRight
  where
  open Group g renaming (inverse to _^-1)
  open Setoid S
  transitive = Equivalence.transitive (Setoid.eq S)
  symmetric = Equivalence.symmetric (Setoid.eq S)
  i : (y · x) · (x ^-1) ∼ (z · x) · (x ^-1)
  i = +WellDefined pr ~refl
  j : y · (x · (x ^-1)) ∼ (z · x) · (x ^-1)
  j = transitive +Associative i
  j' : y · 0G ∼ (z · x) · (x ^-1)
  j' = transitive (+WellDefined ~refl (symmetric invRight)) j
  k : y ∼ (z · x) · (x ^-1)
  k = transitive (symmetric identRight) j'
  l : y ∼ z · (x · (x ^-1))
  l = transitive k (symmetric +Associative)
  m : y ∼ z · 0G
  m = transitive l (+WellDefined ~refl invRight)

replaceGroupOp : {l m : _} {A : Set l} {S : Setoid {l} {m} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b c d w x y z : A} → (Setoid._∼_ S a c) → (Setoid._∼_ S b d) → (Setoid._∼_ S w y) → (Setoid._∼_ S x z) → Setoid._∼_ S (a · b) (w · x) → Setoid._∼_ S (c · d) (y · z)
replaceGroupOp {S = S} {_·_} G a~c b~d w~y x~z pr = transitive (symmetric (+WellDefined a~c b~d)) (transitive pr (+WellDefined w~y x~z))
  where
    open Group G
    open Setoid S
    open Equivalence eq

replaceGroupOpRight : {l m : _} {A : Set l} {S : Setoid {l} {m} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b c x : A} → (Setoid._∼_ S a (b · c)) → (Setoid._∼_ S c x) → (Setoid._∼_ S a (b · x))
replaceGroupOpRight {S = S} {_·_} G a~bc c~x = transitive a~bc (+WellDefined reflexive c~x)
  where
    open Group G
    open Setoid S
    open Equivalence eq

inverseWellDefined : {l m : _} {A : Set l} {S : Setoid {l} {m} A} {_·_ : A → A → A} (G : Group S _·_) → {x y : A} → (Setoid._∼_ S x y) → Setoid._∼_ S (Group.inverse G x) (Group.inverse G y)
inverseWellDefined {S = S} {_·_} G {x} {y} x~y = groupsHaveRightCancellation G x (inverse x) (inverse y) q
  where
    open Group G
    open Setoid S
    open Equivalence eq
    p : inverse x · x ∼ inverse y · y
    p = transitive invLeft (symmetric invLeft)
    q : inverse x · x ∼ inverse y · x
    q = replaceGroupOpRight G {_·_ (inverse x) x} {inverse y} {y} {x} p (symmetric x~y)

rightInversesAreUnique : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → (x : A) → (y : A) → Setoid._∼_ S (y · x) (Group.0G G) → Setoid._∼_ S y (Group.inverse G x)
rightInversesAreUnique {S = S} {_·_} G x y f = transitive i (transitive j (transitive k (transitive l m)))
  where
  open Group G renaming (inverse to _^-1)
  open Setoid S
  open Equivalence eq
  i : y ∼ y · 0G
  j : y · 0G ∼ y · (x · (x ^-1))
  k : y · (x · (x ^-1)) ∼ (y · x) · (x ^-1)
  l : (y · x) · (x ^-1) ∼ 0G · (x ^-1)
  m : 0G · (x ^-1) ∼ x ^-1
  i = symmetric identRight
  j = +WellDefined ~refl (symmetric invRight)
  k = +Associative
  l = +WellDefined f ~refl
  m = identLeft

leftInversesAreUnique : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → {x : A} → {y : A} → Setoid._∼_ S (x · y) (Group.0G G) → Setoid._∼_ S y (Group.inverse G x)
leftInversesAreUnique {S = S} {_·_} G {x} {y} f = rightInversesAreUnique G x y l
  where
    open Group G renaming (inverse to _^-1)
    open Setoid S
    open Equivalence eq
    i : y · (x · y) ∼ y · 0G
    i' : y · (x · y) ∼ y
    j : (y · x) · y ∼ y
    k : (y · x) · y ∼ 0G · y
    l : y · x ∼ 0G
    i = +WellDefined ~refl f
    i' = transitive i identRight
    j = transitive (symmetric +Associative) i'
    k = transitive j (symmetric identLeft)
    l = groupsHaveRightCancellation G y (y · x) 0G k

invTwice : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → (x : A) → Setoid._∼_ S (Group.inverse G (Group.inverse G x)) x
invTwice {S = S} {_·_} G x = symmetric (rightInversesAreUnique G (x ^-1) x invRight)
  where
  open Group G renaming (inverse to _^-1)
  open Setoid S
  open Equivalence eq

fourWay+Associative : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → {r s t u : A} → (Setoid._∼_ S) (r · ((s · t) · u)) ((r · s) · (t · u))
fourWay+Associative {S = S} {_·_} G {r} {s} {t} {u} = transitive p1 (transitive p2 p3)
  where
    open Group G renaming (inverse to _^-1)
    open Setoid S
    open Equivalence eq
    p1 : r · ((s · t) · u) ∼ (r · (s · t)) · u
    p2 : (r · (s · t)) · u ∼ ((r · s) · t) · u
    p3 : ((r · s) · t) · u ∼ (r · s) · (t · u)
    p1 = Group.+Associative G
    p2 = Group.+WellDefined G (Group.+Associative G) reflexive
    p3 = symmetric (Group.+Associative G)

fourWay+Associative' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) {a b c d : A} → (Setoid._∼_ S (((a · b) · c) · d) (a · ((b · c) · d)))
fourWay+Associative' {S = S} G = transitive (symmetric +Associative) (symmetric (fourWay+Associative G))
  where
    open Group G
    open Setoid S
    open Equivalence eq

fourWay+Associative'' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) {a b c d : A} → (Setoid._∼_ S (a · (b · (c · d))) (a · ((b · c) · d)))
fourWay+Associative'' {S = S} {_·_ = _·_} G = transitive +Associative (symmetric (fourWay+Associative G))
  where
    open Group G
    open Setoid S
    open Equivalence eq

invContravariant : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → {x y : A} → (Setoid._∼_ S (Group.inverse G (x · y)) ((Group.inverse G y) · (Group.inverse G x)))
invContravariant {S = S} {_·_} G {x} {y} = ans
  where
    open Group G renaming (inverse to _^-1)
    open Setoid S
    open Equivalence eq
    otherInv = (y ^-1) · (x ^-1)
    many+Associatives : x · ((y · (y ^-1)) · (x ^-1)) ∼ (x · y) · ((y ^-1) · (x ^-1))
    oneMult : (x · y) · otherInv ∼ x · (x ^-1)
    many+Associatives = fourWay+Associative G
    oneMult = symmetric (transitive (Group.+WellDefined G reflexive (transitive (symmetric (Group.identLeft G)) (Group.+WellDefined G (symmetric (Group.invRight G)) reflexive))) many+Associatives)
    otherInvIsInverse : (x · y) · otherInv ∼ 0G
    otherInvIsInverse = transitive oneMult (Group.invRight G)
    ans : (x · y) ^-1 ∼ (y ^-1) · (x ^-1)
    ans = symmetric (leftInversesAreUnique G otherInvIsInverse)

invIdentity : {l m : _} → {A : Set l} → {S : Setoid {l} {m} A} → {_·_ : A → A → A} → (G : Group S _·_) → Setoid._∼_ S ((Group.inverse G) (Group.0G G)) (Group.0G G)
invIdentity {S = S} G = transitive (symmetric identLeft) invRight
  where
    open Group G
    open Setoid S
    open Equivalence eq

transferToRight : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b : A} → Setoid._∼_ S (a · (Group.inverse G b)) (Group.0G G) → Setoid._∼_ S a b
transferToRight {S = S} {_·_ = _·_} G {a} {b} ab-1 = transitive (symmetric (invTwice G a)) (transitive u (invTwice G b))
  where
    open Setoid S
    open Group G
    open Equivalence eq
    t : inverse a ∼ inverse b
    t = symmetric (leftInversesAreUnique G ab-1)
    u : inverse (inverse a) ∼ inverse (inverse b)
    u = inverseWellDefined G t

transferToRight' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b : A} → Setoid._∼_ S (a · b) (Group.0G G) → Setoid._∼_ S a (Group.inverse G b)
transferToRight' {S = S} {_·_ = _·_} G {a} {b} ab-1 = transferToRight G lemma
  where
    open Setoid S
    open Group G
    open Equivalence eq
    lemma : a · (inverse (inverse b)) ∼ 0G
    lemma = transitive (+WellDefined reflexive (invTwice G b)) ab-1

transferToRight'' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b : A} → Setoid._∼_ S a b → Setoid._∼_ S (a · (Group.inverse G b)) (Group.0G G)
transferToRight'' {S = S} {_·_ = _·_} G {a} {b} a~b = transitive (Group.+WellDefined G a~b reflexive) invRight
  where
    open Group G
    open Setoid S
    open Equivalence eq

directSumGroup : {m n o p : _} → {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (h : Group T _·B_) → Group (directSumSetoid S T) (λ x1 y1 → (((_&&_.fst x1) ·A (_&&_.fst y1)) ,, ((_&&_.snd x1) ·B (_&&_.snd y1))))
Group.+WellDefined (directSumGroup {A = A} {B} g h) (s ,, t) (u ,, v) = Group.+WellDefined g s u ,, Group.+WellDefined h t v
Group.0G (directSumGroup {A = A} {B} g h) = (Group.0G g ,, Group.0G h)
Group.inverse (directSumGroup {A = A} {B} g h) (g1 ,, h1) = (Group.inverse g g1) ,, (Group.inverse h h1)
Group.+Associative (directSumGroup {A = A} {B} g h) = Group.+Associative g ,, Group.+Associative h
Group.identRight (directSumGroup {A = A} {B} g h) = Group.identRight g ,, Group.identRight h
Group.identLeft (directSumGroup {A = A} {B} g h) = Group.identLeft g ,, Group.identLeft h
Group.invLeft (directSumGroup {A = A} {B} g h) = Group.invLeft g ,, Group.invLeft h
Group.invRight (directSumGroup {A = A} {B} g h) = Group.invRight g ,, Group.invRight h

directSumAbelianGroup : {m n o p : _} → {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} {underG : Group S _·A_} {underH : Group T _·B_} (G : AbelianGroup underG) (h : AbelianGroup underH) → (AbelianGroup (directSumGroup underG underH))
AbelianGroup.commutative (directSumAbelianGroup {A = A} {B} G H) = AbelianGroup.commutative G ,, AbelianGroup.commutative H

record GroupHom {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) (f : A → B) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Group H
  open Setoid T
  field
    groupHom : {x y : A} → f (x ·A y) ∼ (f x) ·B (f y)
    wellDefined : {x y : A} → Setoid._∼_ S x y → f x ∼ f y

record InjectiveGroupHom {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} {underf : A → B} (f : GroupHom G H underf) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Setoid S renaming (_∼_ to _∼A_)
  open Setoid T renaming (_∼_ to _∼B_)
  field
    injective : SetoidInjection S T underf

imageOfIdentityIsIdentity : {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {B : Set n} {T : Setoid {n} {p} B} {_·A_ : A → A → A} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} {f : A → B} → (hom : GroupHom G H f) → Setoid._∼_ T (f (Group.0G G)) (Group.0G H)
imageOfIdentityIsIdentity {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} {G = G} {H = H} {f = f} hom = Equivalence.symmetric (Setoid.eq T) t
  where
    open Group H
    open Setoid T
    id2 : Setoid._∼_ S (Group.0G G) ((Group.0G G) ·A (Group.0G G))
    id2 = Equivalence.symmetric (Setoid.eq S) (Group.identRight G)
    r : f (Group.0G G) ∼ f (Group.0G G) ·B f (Group.0G G)
    s : 0G ·B f (Group.0G G) ∼ f (Group.0G G) ·B f (Group.0G G)
    t : 0G ∼ f (Group.0G G)
    t = groupsHaveRightCancellation H (f (Group.0G G)) 0G (f (Group.0G G)) s
    s = Equivalence.transitive (Setoid.eq T) identLeft r
    r = Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined hom id2) (GroupHom.groupHom hom)

groupHomsCompose : {m n o r s t : _} {A : Set m} {S : Setoid {m} {r} A} {_+A_ : A → A → A} {B : Set n} {T : Setoid {n} {s} B} {_+B_ : B → B → B} {C : Set o} {U : Setoid {o} {t} C} {_+C_ : C → C → C} {G : Group S _+A_} {H : Group T _+B_} {I : Group U _+C_} {f : A → B} {g : B → C} (fHom : GroupHom G H f) (gHom : GroupHom H I g) → GroupHom G I (g ∘ f)
GroupHom.wellDefined (groupHomsCompose {G = G} {H} {I} {f} {g} fHom gHom) {x} {y} pr = GroupHom.wellDefined gHom (GroupHom.wellDefined fHom pr)
GroupHom.groupHom (groupHomsCompose {S = S} {_+A_ = _·A_} {T = T} {U = U} {_+C_ = _·C_} {G = G} {H} {I} {f} {g} fHom gHom) {x} {y} = answer
  where
    open Group I
    answer : (Setoid._∼_ U) ((g ∘ f) (x ·A y)) ((g ∘ f) x ·C (g ∘ f) y)
    answer = (Equivalence.transitive (Setoid.eq U)) (GroupHom.wellDefined gHom (GroupHom.groupHom fHom {x} {y}) ) (GroupHom.groupHom gHom {f x} {f y})

record GroupIso {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) (f : A → B) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Setoid S renaming (_∼_ to _∼G_)
  open Setoid T renaming (_∼_ to _∼H_)
  field
    groupHom : GroupHom G H f
    bij : SetoidBijection S T f

record GroupsIsomorphic {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) : Set (m ⊔ n ⊔ o ⊔ p) where
  field
    isomorphism : A → B
    proof : GroupIso G H isomorphism

groupIsosCompose : {m n o r s t : _} {A : Set m} {S : Setoid {m} {r} A} {_+A_ : A → A → A} {B : Set n} {T : Setoid {n} {s} B} {_+B_ : B → B → B} {C : Set o} {U : Setoid {o} {t} C} {_+C_ : C → C → C} {G : Group S _+A_} {H : Group T _+B_} {I : Group U _+C_} {f : A → B} {g : B → C} (fHom : GroupIso G H f) (gHom : GroupIso H I g) → GroupIso G I (g ∘ f)
GroupIso.groupHom (groupIsosCompose fHom gHom) = groupHomsCompose (GroupIso.groupHom fHom) (GroupIso.groupHom gHom)
GroupIso.bij (groupIsosCompose {A = A} {S = S} {T = T} {C = C} {U = U} {f = f} {g = g} fHom gHom) = record { inj = record { injective = λ pr → (SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij fHom))) (SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij gHom)) pr) ; wellDefined = +WellDefined } ; surj = record { surjective = surj ; wellDefined = +WellDefined } }
  where
    open Setoid S renaming (_∼_ to _∼A_)
    open Setoid U renaming (_∼_ to _∼C_)
    +WellDefined : {x y : A} → (x ∼A y) → (g (f x) ∼C g (f y))
    +WellDefined = GroupHom.wellDefined (groupHomsCompose (GroupIso.groupHom fHom) (GroupIso.groupHom gHom))
    surj : {x : C} → Sg A (λ a → (g (f a) ∼C x))
    surj {x} with SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij gHom)) {x}
    surj {x} | a , prA with SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij fHom)) {a}
    ... | b , prB = b , transitive (GroupHom.wellDefined (GroupIso.groupHom gHom) prB) prA
      where
        open Equivalence (Setoid.eq U)

record FiniteGroup {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_·_ : A → A → A} (G : Group S _·_) {c : _} (quotientSet : Set c) : Set (a ⊔ b ⊔ c) where
  field
    toSet : SetoidToSet S quotientSet
    finite : FiniteSet quotientSet

groupOrder : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_·_ : A → A → A} {underG : Group S _·_} {c : _} {quotientSet : Set c} (G : FiniteGroup underG quotientSet) → ℕ
groupOrder record { toSet = toSet ; finite = record { size = size ; mapping = mapping ; bij = bij } } = size

--groupIsoInvertible : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d}} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} → (iso : GroupIso G H f) → GroupIso H G (Invertible.inverse (bijectionImpliesInvertible (GroupIso.bijective iso)))
--GroupHom.groupHom (GroupIso.groupHom (groupIsoInvertible {G = G} {H} {f} iso)) {x} {y} = {!!}
--  where
--    open Group G renaming (_·_ to _+G_)
--    open Group H renaming (_·_ to _+H_)
--GroupHom.wellDefined (GroupIso.groupHom (groupIsoInvertible {G = G} {H} {f} iso)) {x} {y} x∼y = {!GroupHom.wellDefined x∼y!}
--GroupIso.bijective (groupIsoInvertible {G = G} {H} {f} iso) = invertibleImpliesBijection (inverseIsInvertible (bijectionImpliesInvertible (GroupIso.bijective iso)))

homRespectsInverse : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} {underF : A → B} → (f : GroupHom G H underF) → {x : A} → Setoid._∼_ T (underF (Group.inverse G x)) (Group.inverse H (underF x))
homRespectsInverse {T = T} {_·A_ = _·A_} {_·B_ = _·B_} {G = G} {H = H} {underF = f} fHom {x} = rightInversesAreUnique H (f x) (f (Group.inverse G x)) (transitive (symmetric (GroupHom.groupHom fHom)) (transitive (GroupHom.wellDefined fHom (Group.invLeft G)) (imageOfIdentityIsIdentity fHom)))
  where
    open Setoid T
    open Equivalence eq

quotientGroupSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {underf : A → B} → (f : GroupHom G H underf) → (Setoid {a} {d} A)
quotientGroupSetoid {A = A} {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {H} {f} fHom = ansSetoid
  where
    open Setoid T
    open Group H
    open Equivalence eq
    ansSetoid : Setoid A
    Setoid._∼_ ansSetoid r s = (f (r ·A (Group.inverse G s))) ∼ 0G
    Equivalence.reflexive (Setoid.eq ansSetoid) {b} = transitive (GroupHom.wellDefined fHom (Group.invRight G)) (imageOfIdentityIsIdentity fHom)
    Equivalence.symmetric (Setoid.eq ansSetoid) {m} {n} pr = i
      where
        g : f (Group.inverse G (m ·A Group.inverse G n)) ∼ 0G
        g = transitive (homRespectsInverse fHom {m ·A Group.inverse G n}) (transitive (inverseWellDefined H pr) (invIdentity H))
        h : f (Group.inverse G (Group.inverse G n) ·A Group.inverse G m) ∼ 0G
        h = transitive (GroupHom.wellDefined fHom (Equivalence.symmetric (Setoid.eq S) (invContravariant G))) g
        i : f (n ·A Group.inverse G m) ∼ 0G
        i = transitive (GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.symmetric (Setoid.eq S) (invTwice G n)) (Equivalence.reflexive (Setoid.eq S)))) h
    Equivalence.transitive (Setoid.eq ansSetoid) {m} {n} {o} prmn prno = transitive (GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.reflexive (Setoid.eq S)) (Equivalence.symmetric (Setoid.eq S) (Group.identLeft G)))) k
      where
        g : f (m ·A Group.inverse G n) ·B f (n ·A Group.inverse G o) ∼ 0G ·B 0G
        g = replaceGroupOp H reflexive reflexive prmn prno reflexive
        h : f (m ·A Group.inverse G n) ·B f (n ·A Group.inverse G o) ∼ 0G
        h = transitive g identLeft
        i : f ((m ·A Group.inverse G n) ·A (n ·A Group.inverse G o)) ∼ 0G
        i = transitive (GroupHom.groupHom fHom) h
        j : f (m ·A (((Group.inverse G n) ·A n) ·A Group.inverse G o)) ∼ 0G
        j = transitive (GroupHom.wellDefined fHom (fourWay+Associative G)) i
        k : f (m ·A ((Group.0G G) ·A Group.inverse G o)) ∼ 0G
        k = transitive (GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.reflexive (Setoid.eq S)) (Group.+WellDefined G (Equivalence.symmetric (Setoid.eq S) (Group.invLeft G)) (Equivalence.reflexive (Setoid.eq S))))) j

quotientGroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {underf : A → B} → (f : GroupHom G H underf) → Group (quotientGroupSetoid G f) _·A_
Group.+WellDefined (quotientGroup {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {H = H} {underf = f} fHom) {x} {y} {m} {n} x~m y~n = ans
  where
    open Setoid T
    open Equivalence (Setoid.eq T)
    p1 : f ((x ·A y) ·A (Group.inverse G (m ·A n))) ∼ f ((x ·A y) ·A ((Group.inverse G n) ·A (Group.inverse G m)))
    p2 : f ((x ·A y) ·A ((Group.inverse G n) ·A (Group.inverse G m))) ∼ f (x ·A ((y ·A (Group.inverse G n)) ·A (Group.inverse G m)))
    p3 : f (x ·A ((y ·A (Group.inverse G n)) ·A (Group.inverse G m))) ∼ (f x) ·B f ((y ·A (Group.inverse G n)) ·A (Group.inverse G m))
    p4 : (f x) ·B f ((y ·A (Group.inverse G n)) ·A (Group.inverse G m)) ∼ (f x) ·B (f (y ·A (Group.inverse G n)) ·B f (Group.inverse G m))
    p5 : (f x) ·B (f (y ·A (Group.inverse G n)) ·B f (Group.inverse G m)) ∼ (f x) ·B (Group.0G H ·B f (Group.inverse G m))
    p6 : (f x) ·B (Group.0G H ·B f (Group.inverse G m)) ∼ (f x) ·B f (Group.inverse G m)
    p7 : (f x) ·B f (Group.inverse G m) ∼ f (x ·A (Group.inverse G m))
    p8 : f (x ·A (Group.inverse G m)) ∼ Group.0G H
    p1 = GroupHom.wellDefined fHom (Group.+WellDefined G (Equivalence.reflexive (Setoid.eq S)) (invContravariant G))
    p2 = GroupHom.wellDefined fHom (Equivalence.symmetric (Setoid.eq S) (fourWay+Associative G))
    p3 = GroupHom.groupHom fHom
    p4 = Group.+WellDefined H reflexive (GroupHom.groupHom fHom)
    p5 = Group.+WellDefined H reflexive (replaceGroupOp H (symmetric y~n) reflexive reflexive reflexive reflexive)
    p6 = Group.+WellDefined H reflexive (Group.identLeft H)
    p7 = symmetric (GroupHom.groupHom fHom)
    p8 = x~m
    ans : f ((x ·A y) ·A (Group.inverse G (m ·A n))) ∼ Group.0G H
    ans = transitive p1 (transitive p2 (transitive p3 (transitive p4 (transitive p5 (transitive p6 (transitive p7 p8))))))
Group.0G (quotientGroup G fHom) = Group.0G G
Group.inverse (quotientGroup G fHom) = Group.inverse G
Group.+Associative (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} {b} {c} = ans
  where
    open Setoid T
    open Equivalence (Setoid.eq T)
    ans : f ((a ·A (b ·A c)) ·A (Group.inverse G ((a ·A b) ·A c))) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transferToRight'' G (Group.+Associative G))) (imageOfIdentityIsIdentity fHom)
Group.identRight (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    transitiveG = Equivalence.transitive (Setoid.eq S)
    ans : f ((a ·A 0G) ·A inverse a) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.+WellDefined G (Group.identRight G) (Equivalence.reflexive (Setoid.eq S))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
Group.identLeft (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    transitiveG = Equivalence.transitive (Setoid.eq S)
    ans : f ((0G ·A a) ·A (inverse a)) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.+WellDefined G (Group.identLeft G) (Equivalence.reflexive (Setoid.eq S))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
Group.invLeft (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {x} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    ans : f ((inverse x ·A x) ·A (inverse 0G)) ∼ (Group.0G H)
    ans = transitive (GroupHom.wellDefined fHom (Equivalence.transitive (Setoid.eq S) (replaceGroupOp G (Equivalence.symmetric (Setoid.eq S) (Group.invLeft G)) (Equivalence.symmetric (Setoid.eq S) (invIdentity G)) (Equivalence.reflexive (Setoid.eq S)) ((Equivalence.reflexive (Setoid.eq S))) ((Equivalence.reflexive (Setoid.eq S)))) (identRight {0G}))) (imageOfIdentityIsIdentity fHom)
Group.invRight (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {x} = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    ans : f ((x ·A inverse x) ·A (inverse 0G)) ∼ (Group.0G H)
    ans = transitive (GroupHom.wellDefined fHom (Equivalence.transitive (Setoid.eq S) (replaceGroupOp G (Equivalence.symmetric (Setoid.eq S) (Group.invRight G)) (Equivalence.symmetric (Setoid.eq S) (invIdentity G)) (Equivalence.reflexive (Setoid.eq S)) (Equivalence.reflexive (Setoid.eq S)) (Equivalence.reflexive (Setoid.eq S))) (identRight {0G}))) (imageOfIdentityIsIdentity fHom)

record Subgroup {a} {b} {c} {d} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) {f : B → A} (hom : GroupHom H G f) : Set (a ⊔ b ⊔ c ⊔ d) where
  open Setoid T renaming (_∼_ to _∼G_)
  open Setoid S renaming (_∼_ to _∼H_)
  field
    fInj : SetoidInjection T S f
{-
quotientHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {f : A → B} → (fHom : GroupHom G H f) → A → A
quotientHom {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {f = f} fHom a = {!!}

quotientInjection : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {f : A → B} → (fHom : GroupHom G H f) → GroupHom (quotientGroup G fHom) G (quotientHom G fHom)
GroupHom.groupHom (quotientInjection {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {f = f} fHom) {x} {y} = {!!}
  where
    open Setoid S
    open Equivalence eq
    open Reflexive reflexiveEq
GroupHom.wellDefined (quotientInjection {S = S} {T = T} {_·A_ = _·A_} G {H = H} {f = f} fHom) {x} {y} x~y = {!!}
  where
    open Group G
    open Setoid S
    open Setoid T renaming (_∼_ to _∼T_)
    open Equivalence (Setoid.eq S)
    open Reflexive reflexiveEq
    have : f (x ·A inverse y) ∼T Group.0G H
    have = x~y
    need : x ∼ y
    need = {!!}

quotientIsSubgroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} → {f : A → B} → {fHom : GroupHom G H f} → Subgroup G (quotientGroup G fHom) (quotientInjection G fHom)
quotientIsSubgroup = {!!}

-}
subgroupOfAbelianIsAbelian : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : B → A} {fHom : GroupHom H G f} → Subgroup G H fHom → AbelianGroup G → AbelianGroup H
AbelianGroup.commutative (subgroupOfAbelianIsAbelian {S = S} {_+B_ = _+B_} {fHom = fHom} record { fInj = fInj } record { commutative = commutative }) {x} {y} = SetoidInjection.injective fInj (transitive (GroupHom.groupHom fHom) (transitive commutative (symmetric (GroupHom.groupHom fHom))))
  where
    open Setoid S
    open Equivalence eq

abelianIsGroupProperty : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} → GroupsIsomorphic G H → AbelianGroup H → AbelianGroup G
abelianIsGroupProperty iso abH = subgroupOfAbelianIsAbelian {fHom = GroupIso.groupHom (GroupsIsomorphic.proof iso)} (record { fInj = SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof iso)) }) abH
