{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Naturals
open import FinSet

module Groups where
    record Group {lvl1 lvl2} {A : Set lvl1} (S : Setoid {lvl1} {lvl2} A) (_·_ : A → A → A) : Set (lsuc lvl1 ⊔ lvl2) where
      open Setoid S
      field
        wellDefined : {m n x y : A} → (m ∼ x) → (n ∼ y) → (m · n) ∼ (x · y)
        identity : A
        inverse : A → A
        multAssoc : {a b c : A} → (a · (b · c)) ∼ (a · b) · c
        multIdentRight : {a : A} → (a · identity) ∼ a
        multIdentLeft : {a : A} → (identity · a) ∼ a
        invLeft : {a : A} → (inverse a) · a ∼ identity
        invRight : {a : A} → a · (inverse a) ∼ identity

    reflGroupWellDefined : {lvl : _} {A : Set lvl} {m n x y : A} {op : A → A → A} → m ≡ x → n ≡ y → (op m n) ≡ (op x y)
    reflGroupWellDefined {lvl} {A} {m} {n} {.m} {.n} {op} refl refl = refl

    record AbelianGroup {a} {b} {A : Set a} {S : Setoid {a} {b} A} {_·_ : A → A → A} (G : Group S _·_) : Set (lsuc a ⊔ b) where
      open Setoid S
      field
        commutative : {a b : A} → (a · b) ∼ (b · a)

    groupsHaveLeftCancellation : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → (x y z : A) → (Setoid._∼_ S (x · y) (x · z)) → (Setoid._∼_ S y z)
    groupsHaveLeftCancellation {_·_ = _·_} {S} g x y z pr = o
      where
      open Group g renaming (inverse to _^-1) renaming (identity to e)
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
      j : ((x ^-1) · x) · y ∼ (x ^-1) · (x · z)
      j = transitive (symmetric (multAssoc {x ^-1} {x} {y})) (wellDefined ~refl pr)
      k : ((x ^-1) · x) · y ∼ ((x ^-1) · x) · z
      k = transitive j multAssoc
      l : e · y ∼ ((x ^-1) · x) · z
      l = transitive (wellDefined (symmetric invLeft) ~refl) k
      m : e · y ∼ e · z
      m = transitive l (wellDefined invLeft ~refl)
      n : y ∼ e · z
      n = transitive (symmetric multIdentLeft) m
      o : y ∼ z
      o = transitive n multIdentLeft

    groupsHaveRightCancellation : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → (x y z : A) → (Setoid._∼_ S (y · x) (z · x)) → (Setoid._∼_ S y z)
    groupsHaveRightCancellation {_·_ = _·_} {S} g x y z pr = transitive m multIdentRight
      where
      open Group g renaming (inverse to _^-1) renaming (identity to e)
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
      i : (y · x) · (x ^-1) ∼ (z · x) · (x ^-1)
      i = wellDefined pr ~refl
      j : y · (x · (x ^-1)) ∼ (z · x) · (x ^-1)
      j = transitive multAssoc i
      j' : y · e ∼ (z · x) · (x ^-1)
      j' = transitive (wellDefined ~refl (symmetric invRight)) j
      k : y ∼ (z · x) · (x ^-1)
      k = transitive (symmetric multIdentRight) j'
      l : y ∼ z · (x · (x ^-1))
      l = transitive k (symmetric multAssoc)
      m : y ∼ z · e
      m = transitive l (wellDefined ~refl invRight)

    identityIsUnique : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → (e : A) → ((b : A) → (Setoid._∼_ S (b · e) b)) → (Setoid._∼_ S e (Group.identity G))
    identityIsUnique {S = S} {_·_} g thing fb = transitive (symmetric multIdentLeft) (fb e)
      where
        open Group g renaming (inverse to _^-1) renaming (identity to e)
        open Setoid S
        open Transitive (Equivalence.transitiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)

    replaceGroupOp : {l m : _} {A : Set l} {S : Setoid {l} {m} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b c d w x y z : A} → (Setoid._∼_ S a c) → (Setoid._∼_ S b d) → (Setoid._∼_ S w y) → (Setoid._∼_ S x z) → Setoid._∼_ S (a · b) (w · x) → Setoid._∼_ S (c · d) (y · z)
    replaceGroupOp {S = S} {_·_} G a~c b~d w~y x~z pr = transitive (symmetric (wellDefined a~c b~d)) (transitive pr (wellDefined w~y x~z))
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Transitive transitiveEq
        open Symmetric symmetricEq

    replaceGroupOpRight : {l m : _} {A : Set l} {S : Setoid {l} {m} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b c x : A} → (Setoid._∼_ S a (b · c)) → (Setoid._∼_ S c x) → (Setoid._∼_ S a (b · x))
    replaceGroupOpRight {S = S} {_·_} G a~bc c~x = transitive a~bc (wellDefined reflexive c~x)
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Transitive transitiveEq
        open Reflexive reflexiveEq

    inverseWellDefined : {l m : _} {A : Set l} {S : Setoid {l} {m} A} {_·_ : A → A → A} (G : Group S _·_) → {x y : A} → (Setoid._∼_ S x y) → Setoid._∼_ S (Group.inverse G x) (Group.inverse G y)
    inverseWellDefined {S = S} {_·_} G {x} {y} x~y = groupsHaveRightCancellation G x (inverse x) (inverse y) q
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Transitive transitiveEq
        open Symmetric symmetricEq
        p : inverse x · x ∼ inverse y · y
        p = transitive invLeft (symmetric invLeft)
        q : inverse x · x ∼ inverse y · x
        q = replaceGroupOpRight G {_·_ (inverse x) x} {inverse y} {y} {x} p (symmetric x~y)

    rightInversesAreUnique : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → (x : A) → (y : A) → Setoid._∼_ S (y · x) (Group.identity G) → Setoid._∼_ S y (Group.inverse G x)
    rightInversesAreUnique {S = S} {_·_} G x y f = transitive i (transitive j (transitive k (transitive l m)))
      where
      open Group G renaming (inverse to _^-1) renaming (identity to e)
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
      i : y ∼ y · e
      j : y · e ∼ y · (x · (x ^-1))
      k : y · (x · (x ^-1)) ∼ (y · x) · (x ^-1)
      l : (y · x) · (x ^-1) ∼ e · (x ^-1)
      m : e · (x ^-1) ∼ x ^-1
      i = symmetric multIdentRight
      j = wellDefined ~refl (symmetric invRight)
      k = multAssoc
      l = wellDefined f ~refl
      m = multIdentLeft

    leftInversesAreUnique : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → {x : A} → {y : A} → Setoid._∼_ S (x · y) (Group.identity G) → Setoid._∼_ S y (Group.inverse G x)
    leftInversesAreUnique {S = S} {_·_} G {x} {y} f = rightInversesAreUnique G x y l
      where
        open Group G renaming (inverse to _^-1) renaming (identity to e)
        open Setoid S
        open Transitive (Equivalence.transitiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)
        i : y · (x · y) ∼ y · e
        i' : y · (x · y) ∼ y
        j : (y · x) · y ∼ y
        k : (y · x) · y ∼ e · y
        l : y · x ∼ e
        i = wellDefined ~refl f
        i' = transitive i multIdentRight
        j = transitive (symmetric multAssoc) i'
        k = transitive j (symmetric multIdentLeft)
        l = groupsHaveRightCancellation G y (y · x) e k

    invTwice : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → (x : A) → Setoid._∼_ S (Group.inverse G (Group.inverse G x)) x
    invTwice {S = S} {_·_} G x = symmetric (rightInversesAreUnique G (x ^-1) x invRight)
      where
      open Group G renaming (inverse to _^-1) renaming (identity to e)
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)

    fourWayAssoc : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → {r s t u : A} → (Setoid._∼_ S) (r · ((s · t) · u)) ((r · s) · (t · u))
    fourWayAssoc {S = S} {_·_} G {r} {s} {t} {u} = transitive p1 (transitive p2 p3)
      where
        open Group G renaming (inverse to _^-1) renaming (identity to e)
        open Setoid S
        open Equivalence eq
        open Transitive transitiveEq
        open Reflexive reflexiveEq
        open Symmetric symmetricEq
        p1 : r · ((s · t) · u) ∼ (r · (s · t)) · u
        p2 : (r · (s · t)) · u ∼ ((r · s) · t) · u
        p3 : ((r · s) · t) · u ∼ (r · s) · (t · u)
        p1 = Group.multAssoc G
        p2 = Group.wellDefined G (Group.multAssoc G) reflexive
        p3 = symmetric (Group.multAssoc G)

    fourWayAssoc' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) {a b c d : A} → (Setoid._∼_ S (((a · b) · c) · d) (a · ((b · c) · d)))
    fourWayAssoc' {S = S} G = transitive (symmetric multAssoc) (symmetric (fourWayAssoc G))
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Transitive transitiveEq
        open Symmetric symmetricEq

    fourWayAssoc'' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) {a b c d : A} → (Setoid._∼_ S (a · (b · (c · d))) (a · ((b · c) · d)))
    fourWayAssoc'' {S = S} {_·_ = _·_} G = transitive multAssoc (symmetric (fourWayAssoc G))
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Transitive transitiveEq
        open Symmetric symmetricEq

    invContravariant : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → (x y : A) → (Setoid._∼_ S (Group.inverse G (x · y)) ((Group.inverse G y) · (Group.inverse G x)))
    invContravariant {S = S} {_·_} G x y = ans
      where
        open Group G renaming (inverse to _^-1) renaming (identity to e)
        open Setoid S
        open Equivalence eq
        open Transitive transitiveEq
        open Symmetric symmetricEq
        open Reflexive reflexiveEq
        otherInv = (y ^-1) · (x ^-1)
        manyAssocs : x · ((y · (y ^-1)) · (x ^-1)) ∼ (x · y) · ((y ^-1) · (x ^-1))
        oneMult : (x · y) · otherInv ∼ x · (x ^-1)
        manyAssocs = fourWayAssoc G
        oneMult = symmetric (transitive (Group.wellDefined G reflexive (transitive (symmetric (Group.multIdentLeft G)) (Group.wellDefined G (symmetric (Group.invRight G)) reflexive))) manyAssocs)
        otherInvIsInverse : (x · y) · otherInv ∼ e
        otherInvIsInverse = transitive oneMult (Group.invRight G)
        ans : (x · y) ^-1 ∼ (y ^-1) · (x ^-1)
        ans = symmetric (leftInversesAreUnique G otherInvIsInverse)

    invIdentity : {l m : _} → {A : Set l} → {S : Setoid {l} {m} A} → {_·_ : A → A → A} → (G : Group S _·_) → Setoid._∼_ S ((Group.inverse G) (Group.identity G)) (Group.identity G)
    invIdentity {S = S} G = transitive (symmetric multIdentLeft) invRight
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Symmetric symmetricEq
        open Transitive transitiveEq

    transferToRight : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b : A} → Setoid._∼_ S (a · (Group.inverse G b)) (Group.identity G) → Setoid._∼_ S a b
    transferToRight {S = S} {_·_ = _·_} G {a} {b} ab-1 = transitive (symmetric (invTwice G a)) (transitive u (invTwice G b))
      where
        open Setoid S
        open Group G
        open Equivalence eq
        open Symmetric symmetricEq
        open Transitive transitiveEq
        t : inverse a ∼ inverse b
        t = symmetric (leftInversesAreUnique G ab-1)
        u : inverse (inverse a) ∼ inverse (inverse b)
        u = inverseWellDefined G t

    transferToRight' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b : A} → Setoid._∼_ S (a · b) (Group.identity G) → Setoid._∼_ S a (Group.inverse G b)
    transferToRight' {S = S} {_·_ = _·_} G {a} {b} ab-1 = transferToRight G lemma
      where
        open Setoid S
        open Group G
        open Equivalence eq
        open Symmetric symmetricEq
        open Transitive transitiveEq
        open Reflexive reflexiveEq
        lemma : a · (inverse (inverse b)) ∼ identity
        lemma = transitive (wellDefined reflexive (invTwice G b)) ab-1

    transferToRight'' : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → {a b : A} → Setoid._∼_ S a b → Setoid._∼_ S (a · (Group.inverse G b)) (Group.identity G)
    transferToRight'' {S = S} {_·_ = _·_} G {a} {b} a~b = transitive (Group.wellDefined G a~b reflexive) invRight
      where
        open Group G
        open Setoid S
        open Transitive (Equivalence.transitiveEq eq)
        open Reflexive (Equivalence.reflexiveEq eq)

    directSumGroup : {m n o p : _} → {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (h : Group T _·B_) → Group (directSumSetoid S T) (λ x1 y1 → (((_&&_.fst x1) ·A (_&&_.fst y1)) ,, ((_&&_.snd x1) ·B (_&&_.snd y1))))
    Group.wellDefined (directSumGroup {A = A} {B} g h) (s ,, t) (u ,, v) = Group.wellDefined g s u ,, Group.wellDefined h t v
    Group.identity (directSumGroup {A = A} {B} g h) = (Group.identity g ,, Group.identity h)
    Group.inverse (directSumGroup {A = A} {B} g h) (g1 ,, h1) = (Group.inverse g g1) ,, (Group.inverse h h1)
    Group.multAssoc (directSumGroup {A = A} {B} g h) = Group.multAssoc g ,, Group.multAssoc h
    Group.multIdentRight (directSumGroup {A = A} {B} g h) = Group.multIdentRight g ,, Group.multIdentRight h
    Group.multIdentLeft (directSumGroup {A = A} {B} g h) = Group.multIdentLeft g ,, Group.multIdentLeft h
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

    imageOfIdentityIsIdentity : {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {B : Set n} {T : Setoid {n} {p} B} {_·A_ : A → A → A} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} {f : A → B} → (hom : GroupHom G H f) → Setoid._∼_ T (f (Group.identity G)) (Group.identity H)
    imageOfIdentityIsIdentity {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} {G = G} {H = H} {f = f} hom = Symmetric.symmetric (Equivalence.symmetricEq eq) t
      where
        open Group H
        open Setoid T
        id2 : Setoid._∼_ S (Group.identity G) ((Group.identity G) ·A (Group.identity G))
        id2 = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (Group.multIdentRight G)
        r : f (Group.identity G) ∼ f (Group.identity G) ·B f (Group.identity G)
        s : identity ·B f (Group.identity G) ∼ f (Group.identity G) ·B f (Group.identity G)
        t : identity ∼ f (Group.identity G)
        t = groupsHaveRightCancellation H (f (Group.identity G)) identity (f (Group.identity G)) s
        s = Transitive.transitive (Equivalence.transitiveEq eq) multIdentLeft r
        r = Transitive.transitive (Equivalence.transitiveEq eq) (GroupHom.wellDefined hom id2) (GroupHom.groupHom hom)

    groupHomsCompose : {m n o r s t : _} {A : Set m} {S : Setoid {m} {r} A} {_+A_ : A → A → A} {B : Set n} {T : Setoid {n} {s} B} {_+B_ : B → B → B} {C : Set o} {U : Setoid {o} {t} C} {_+C_ : C → C → C} {G : Group S _+A_} {H : Group T _+B_} {I : Group U _+C_} {f : A → B} {g : B → C} (fHom : GroupHom G H f) (gHom : GroupHom H I g) → GroupHom G I (g ∘ f)
    GroupHom.wellDefined (groupHomsCompose {G = G} {H} {I} {f} {g} fHom gHom) {x} {y} pr = GroupHom.wellDefined gHom (GroupHom.wellDefined fHom pr)
    GroupHom.groupHom (groupHomsCompose {S = S} {_+A_ = _·A_} {T = T} {U = U} {_+C_ = _·C_} {G = G} {H} {I} {f} {g} fHom gHom) {x} {y} = answer
      where
        open Group I
        answer : (Setoid._∼_ U) ((g ∘ f) (x ·A y)) ((g ∘ f) x ·C (g ∘ f) y)
        answer = (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq U))) (GroupHom.wellDefined gHom (GroupHom.groupHom fHom {x} {y}) ) (GroupHom.groupHom gHom {f x} {f y})

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
    GroupIso.bij (groupIsosCompose {A = A} {S = S} {T = T} {C = C} {U = U} {f = f} {g = g} fHom gHom) = record { inj = record { injective = λ pr → (SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij fHom))) (SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij gHom)) pr) ; wellDefined = wellDefined } ; surj = record { surjective = surj ; wellDefined = wellDefined } }
      where
        open Setoid S renaming (_∼_ to _∼A_)
        open Setoid U renaming (_∼_ to _∼C_)
        wellDefined : {x y : A} → (x ∼A y) → (g (f x) ∼C g (f y))
        wellDefined = GroupHom.wellDefined (groupHomsCompose (GroupIso.groupHom fHom) (GroupIso.groupHom gHom))
        surj : {x : C} → Sg A (λ a → (g (f a) ∼C x))
        surj {x} with SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij gHom)) {x}
        surj {x} | a , prA with SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij fHom)) {a}
        ... | b , prB = b , transitive (GroupHom.wellDefined (GroupIso.groupHom gHom) prB) prA
          where
            open Transitive (Equivalence.transitiveEq (Setoid.eq U))

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
        open Transitive transitiveEq
        open Symmetric symmetricEq

    quotientGroupSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {underf : A → B} → (f : GroupHom G H underf) → (Setoid {a} {d} A)
    quotientGroupSetoid {A = A} {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {H} {f} fHom = ansSetoid
      where
        open Setoid T
        open Group H
        open Equivalence eq
        open Transitive transitiveEq
        open Reflexive reflexiveEq
        ansSetoid : Setoid A
        Setoid._∼_ ansSetoid r s = (f (r ·A (Group.inverse G s))) ∼ identity
        Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq ansSetoid)) {b} = transitive (GroupHom.wellDefined fHom (Group.invRight G)) (imageOfIdentityIsIdentity fHom)
        Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq ansSetoid)) {m} {n} pr = i
          where
            g : f (Group.inverse G (m ·A Group.inverse G n)) ∼ identity
            g = transitive (homRespectsInverse fHom {m ·A Group.inverse G n}) (transitive (inverseWellDefined H pr) (invIdentity H))
            h : f (Group.inverse G (Group.inverse G n) ·A Group.inverse G m) ∼ identity
            h = transitive (GroupHom.wellDefined fHom (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (invContravariant G m (Group.inverse G n)))) g
            i : f (n ·A Group.inverse G m) ∼ identity
            i = transitive (GroupHom.wellDefined fHom (Group.wellDefined G (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (invTwice G n)) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))))) h
        Transitive.transitive (Equivalence.transitiveEq (Setoid.eq ansSetoid)) {m} {n} {o} prmn prno = transitive (GroupHom.wellDefined fHom (Group.wellDefined G (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (Group.multIdentLeft G)))) k
          where
            g : f (m ·A Group.inverse G n) ·B f (n ·A Group.inverse G o) ∼ identity ·B identity
            g = replaceGroupOp H reflexive reflexive prmn prno reflexive
            h : f (m ·A Group.inverse G n) ·B f (n ·A Group.inverse G o) ∼ identity
            h = transitive g multIdentLeft
            i : f ((m ·A Group.inverse G n) ·A (n ·A Group.inverse G o)) ∼ identity
            i = transitive (GroupHom.groupHom fHom) h
            j : f (m ·A (((Group.inverse G n) ·A n) ·A Group.inverse G o)) ∼ identity
            j = transitive (GroupHom.wellDefined fHom (fourWayAssoc G)) i
            k : f (m ·A ((Group.identity G) ·A Group.inverse G o)) ∼ identity
            k = transitive (GroupHom.wellDefined fHom (Group.wellDefined G (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (Group.wellDefined G (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (Group.invLeft G)) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)))))) j

    quotientGroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {underf : A → B} → (f : GroupHom G H underf) → Group (quotientGroupSetoid G f) _·A_
    Group.wellDefined (quotientGroup {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G {H = H} {underf = f} fHom) {x} {y} {m} {n} x~m y~n = ans
      where
        open Setoid T
        open Equivalence (Setoid.eq T)
        open Symmetric symmetricEq
        open Transitive transitiveEq
        p1 : f ((x ·A y) ·A (Group.inverse G (m ·A n))) ∼ f ((x ·A y) ·A ((Group.inverse G n) ·A (Group.inverse G m)))
        p2 : f ((x ·A y) ·A ((Group.inverse G n) ·A (Group.inverse G m))) ∼ f (x ·A ((y ·A (Group.inverse G n)) ·A (Group.inverse G m)))
        p3 : f (x ·A ((y ·A (Group.inverse G n)) ·A (Group.inverse G m))) ∼ (f x) ·B f ((y ·A (Group.inverse G n)) ·A (Group.inverse G m))
        p4 : (f x) ·B f ((y ·A (Group.inverse G n)) ·A (Group.inverse G m)) ∼ (f x) ·B (f (y ·A (Group.inverse G n)) ·B f (Group.inverse G m))
        p5 : (f x) ·B (f (y ·A (Group.inverse G n)) ·B f (Group.inverse G m)) ∼ (f x) ·B (Group.identity H ·B f (Group.inverse G m))
        p6 : (f x) ·B (Group.identity H ·B f (Group.inverse G m)) ∼ (f x) ·B f (Group.inverse G m)
        p7 : (f x) ·B f (Group.inverse G m) ∼ f (x ·A (Group.inverse G m))
        p8 : f (x ·A (Group.inverse G m)) ∼ Group.identity H
        p1 = GroupHom.wellDefined fHom (Group.wellDefined G (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (invContravariant G m n))
        p2 = GroupHom.wellDefined fHom (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (fourWayAssoc G))
        p3 = GroupHom.groupHom fHom
        p4 = Group.wellDefined H (Reflexive.reflexive reflexiveEq) (GroupHom.groupHom fHom)
        p5 = Group.wellDefined H (Reflexive.reflexive reflexiveEq) (replaceGroupOp H (symmetric y~n) (Reflexive.reflexive reflexiveEq) (Reflexive.reflexive reflexiveEq) (Reflexive.reflexive reflexiveEq) (Reflexive.reflexive reflexiveEq))
        p6 = Group.wellDefined H (Reflexive.reflexive reflexiveEq) (Group.multIdentLeft H)
        p7 = Symmetric.symmetric symmetricEq (GroupHom.groupHom fHom)
        p8 = x~m
        ans : f ((x ·A y) ·A (Group.inverse G (m ·A n))) ∼ Group.identity H
        ans = transitive p1 (transitive p2 (transitive p3 (transitive p4 (transitive p5 (transitive p6 (transitive p7 p8))))))
    Group.identity (quotientGroup G fHom) = Group.identity G
    Group.inverse (quotientGroup G fHom) = Group.inverse G
    Group.multAssoc (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} {b} {c} = ans
      where
        open Setoid T
        open Equivalence (Setoid.eq T)
        open Transitive transitiveEq
        ans : f ((a ·A (b ·A c)) ·A (Group.inverse G ((a ·A b) ·A c))) ∼ Group.identity H
        ans = transitive (GroupHom.wellDefined fHom (transferToRight'' G (Group.multAssoc G))) (imageOfIdentityIsIdentity fHom)
    Group.multIdentRight (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} = ans
      where
        open Group G
        open Setoid T
        open Equivalence eq
        open Transitive transitiveEq
        open Transitive (Equivalence.transitiveEq (Setoid.eq S)) renaming (transitive to transitiveG)
        ans : f ((a ·A identity) ·A inverse a) ∼ Group.identity H
        ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.wellDefined G (Group.multIdentRight G) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
    Group.multIdentLeft (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {a} = ans
      where
        open Group G
        open Setoid T
        open Equivalence eq
        open Transitive transitiveEq
        open Transitive (Equivalence.transitiveEq (Setoid.eq S)) renaming (transitive to transitiveG)
        ans : f ((identity ·A a) ·A (inverse a)) ∼ Group.identity H
        ans = transitive (GroupHom.wellDefined fHom (transitiveG (Group.wellDefined G (Group.multIdentLeft G) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)))) (Group.invRight G))) (imageOfIdentityIsIdentity fHom)
    Group.invLeft (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {x} = ans
      where
        open Group G
        open Setoid T
        open Equivalence eq
        open Transitive transitiveEq
        ans : f ((inverse x ·A x) ·A (inverse identity)) ∼ (Group.identity H)
        ans = transitive (GroupHom.wellDefined fHom (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) (replaceGroupOp G (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (Group.invLeft G)) (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (invIdentity G)) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) ((Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)))) ((Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))))) (multIdentRight {identity}))) (imageOfIdentityIsIdentity fHom)
    Group.invRight (quotientGroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {underf = f} fHom) {x} = ans
      where
        open Group G
        open Setoid T
        open Equivalence eq
        open Transitive transitiveEq
        ans : f ((x ·A inverse x) ·A (inverse identity)) ∼ (Group.identity H)
        ans = transitive (GroupHom.wellDefined fHom (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) (replaceGroupOp G (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (Group.invRight G)) (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) (invIdentity G)) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)))) (multIdentRight {identity}))) (imageOfIdentityIsIdentity fHom)

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
        have : f (x ·A inverse y) ∼T Group.identity H
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
        open Transitive (Equivalence.transitiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)

    abelianIsGroupProperty : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} → GroupsIsomorphic G H → AbelianGroup H → AbelianGroup G
    abelianIsGroupProperty iso abH = subgroupOfAbelianIsAbelian {fHom = GroupIso.groupHom (GroupsIsomorphic.proof iso)} (record { fInj = SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof iso)) }) abH
