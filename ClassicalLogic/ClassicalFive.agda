{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae


module ClassicalLogic.ClassicalFive where

em = {A : Set} → (A || (A → False))
dne = {A : Set} → ((A → False) → False) → A
peirce = {A B : Set} → ((A → B) → A) → A
iad = {A B : Set} → (A → B) → ((A → False) || B)

emToDne : em → dne
emToDne em {A} pr with em {A}
emToDne em {A} pr | inl x = x
emToDne em {A} pr | inr x = exFalso (pr x)

dneToPeirce : dne → peirce
dneToPeirce dne {A} {B} aba = dne (λ z → z (aba (λ z₁ → dne (λ _ → z z₁))))

peirceToIad : peirce → iad
peirceToIad peirce {A} {B} aToB = peirce (λ z → inl (λ x → z (inr (aToB x))))

iadToEm : iad → em
iadToEm iad {A} with (iad {A} {A} (λ i → i))
iadToEm iad {A} | inl x = inr x
iadToEm iad {A} | inr x = inl x

dem = {A B : Set} → (((A → False) && (B → False)) → False) → A || B

demToEm : dem → em
demToEm dem {A} = dem (λ z → _&&_.snd z (_&&_.fst z))

emToDem : em → dem
emToDem em {A} {B} pr with em {A}
emToDem em {A} {B} pr | inl x = inl x
emToDem em {A} {B} pr | inr x with em {B}
emToDem em {A} {B} pr | inr x | inl x₁ = inr x₁
emToDem em {A} {B} pr | inr x | inr y = exFalso (pr (x ,, y))

isContr : {a : _} (A : Set a) → Set a
isContr T = (x y : T) → x ≡ y

pr : {a : _} {A : Set a} → {x : A} → isContr (Sg A (λ y → x ≡ y))
pr {A = A} {.a} (a , refl) (.a , refl) = refl
