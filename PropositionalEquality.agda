{-# OPTIONS --cubical-compatible --safe #-}
module PropositionalEquality where

open import MLTTPrelude

open import Agda.Builtin.Equality public

sym : ∀ {ℓ} {A : Set ℓ} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

infixr 20 _∙_

_∙_ : ∀ {ℓ} {A : Set ℓ} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

subst : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A}
      → x ≡ y → P x → P y
subst P refl p = p

cong : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {ℓ ℓ' ℓ″} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ″}
      → {x y : A} {u v : B}
      → (f : A → B → C) → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

J : ∀ {ℓ ℓ'} {A : Set ℓ} {x y : A}
  → (P : ∀ y → x ≡ y → Set ℓ')
  → P x refl → (p : x ≡ y) → P y p
J P d refl = d

lCancel : ∀ {ℓ} {A : Set ℓ} {x y : A}
        → (p : x ≡ y) → sym p ∙ p ≡ refl
lCancel refl = refl

isProp isSet : ∀ {ℓ} → Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y
isSet  A = (x y : A) → isProp (x ≡ y)

Discrete : ∀ {ℓ} → Set ℓ → Set ℓ
Discrete A = (x y : A) → Dec (x ≡ y)
