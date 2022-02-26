{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT.Ident where

data Id (X : Set) : X → X → Set  where
 refl : (x : X) → Id X x x

_≡_ : {X : Set} → X → X → Set
x ≡ y = Id _ x y

𝕁 : {X : Set}
  → (A : (x y : X) → x ≡ y → Set)
  → ((x : X) → A x x (refl x))
  → (x y : X) → (p : x ≡ y) → A x y p
𝕁 A f x x (refl x) = f x

ℍ : {X : Set}
  → (x : X)
  → (B : (y : X) → x ≡ y → Set)
  → B x (refl x)
  → (y : X) → (p : x ≡ y) → B y p
ℍ x B b x (refl x) = b

𝕁' : {X : Set}
  → (A : (x y : X) → x ≡ y → Set)
  → ((x : X) → A x x (refl x))
  → (x y : X) → (p : x ≡ y) → A x y p
𝕁' A f x = ℍ x (A x) (f x)

-- Defining `ℍ` in terms of `𝕁`.

id : {X : Set} → X → X
id x = x

transport : {X : Set} → (f : X → Set) → (x y : X) → (x ≡ y) → f x → f y
transport f = 𝕁 (λ x y p → f x → f y) (λ x → id)

data Σ (A : Set) (p : A → Set) : Set  where
  _,_ : (x : A) → p x → Σ A p

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

curry : {A : Set} {B : A → Set} → ((x : A) → B x → Set) → Σ A B → Set
curry f (x , y) = f x y

-- This is just for the "Note" below.
singl : (A : Set) → A → Set
singl A x = Σ A (λ y → x ≡ y)

-- Note:  `≡` in the conclusion is WRT `Id (singl X x)`.
lemma : {X : Set} → (x y : X) → (p : x ≡ y) → (x , refl x) ≡ (y , p)
lemma = 𝕁 (λ x y p → (x , refl x) ≡ (y , p)) (λ x → refl (x , refl x))

ℍ' : {X : Set}
  → (x : X)
  → (B : (y : X) → x ≡ y → Set)
  → B x (refl x)
  → (y : X) → (p : x ≡ y) → B y p
ℍ' x B b y p = transport (curry B) (x , refl x) (y , p) (lemma x y p) b

