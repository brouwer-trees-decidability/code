----------------------------------------------------------------------------------------------------
-- The "if-and-only-if" relation
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --guardedness --erasure #-}

module Iff where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import PropTrunc

private
 variable
  ℓ₁ ℓ₂ ℓ₃ : Level

_↔_ : (A : Type ℓ₁) (B : Type ℓ₂) → Type _
A ↔ B = (A → B) × (B → A)

infix   1 _↔_

lr : {A : Type ℓ₁}{B : Type ℓ₂} → A ↔ B → A → B
lr = fst

rl : {A : Type ℓ₁}{B : Type ℓ₂} → A ↔ B → B → A
rl = snd

isProp↔ : {A : Type ℓ₁}{B : Type ℓ₂}
        → isProp A → isProp B → isProp (A ↔ B)
isProp↔ pA pB = isProp× (isPropΠ (λ _ → pB)) (isPropΠ (λ _ → pA))

↔-refl : {A : Type ℓ₁} → A ↔ A
↔-refl = (λ a → a) , (λ a → a)

↔-sym : {A : Type ℓ₁}{B : Type ℓ₂} → A ↔ B → B ↔ A
↔-sym (l , r) = (r , l)

↔-trans : {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (A ↔ B) → (B ↔ C) → (A ↔ C)
↔-trans A↔B B↔C = (lr B↔C ∘ lr A↔B) , (rl A↔B ∘ rl B↔C)

_↔⟨_⟩_ : (A : Type ℓ₁) {B : Type ℓ₂} {C : Type ℓ₃}
         → (A ↔ B) → (B ↔ C) → (A ↔ C)
A ↔⟨ A↔B ⟩ B↔C = ↔-trans A↔B B↔C

_↔∎ : (A : Type ℓ₁) → A ↔ A
A ↔∎ = ↔-refl

infixr  0 _↔⟨_⟩_
infix   1 _↔∎

∥-∥↔ : {A : Type ℓ₁}{B : Type ℓ₂} → A ↔ B → ∥ A ∥ ↔ ∥ B ∥
∥-∥↔ p = ∥-∥map (lr p) , ∥-∥map (rl p)
