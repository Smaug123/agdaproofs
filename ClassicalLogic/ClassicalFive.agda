{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae


module ClassicalLogic.ClassicalFive where

em = {A : Set} → (A || (A → False))
dne = {A : Set} → ((A → False) → False) → A
peirce = {A B : Set} → ((A → B) → A) → A
iad = {A B : Set} → (A → B) → ((A → False) || B)
dem = {A B : Set} → (((A → False) && (B → False)) → False) → A || B

emToDne : em → dne
emToDne em {A} pr with em {A}
emToDne em {A} pr | inl x = x
emToDne em {A} pr | inr x = exFalso (pr x)

dneToPeirce : dne → peirce
dneToPeirce dne {A} {B} aba = dne (λ z → z (aba (λ a → dne (λ _ → z a))))

peirceToIad : peirce → iad
peirceToIad peirce {A} {B} aToB = peirce (λ z → inl (λ x → z (inr (aToB x))))

iadToDem : iad → dem
iadToDem iad {A} {B} x with iad {A} {A} (λ i → i)
iadToDem iad {A} {B} x | inl notA with iad {B} {B} (λ i → i)
iadToDem iad {A} {B} x | inl notA | inl notB = exFalso (x (notA ,, notB))
iadToDem iad {A} {B} x | inl notA | inr b = inr b
iadToDem iad {A} {B} x | inr a = inl a

demToEm : dem → em
demToEm dem {A} = dem (λ z → _&&_.snd z (_&&_.fst z))
