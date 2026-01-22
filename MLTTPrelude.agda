{-# OPTIONS --cubical-compatible --safe #-}
module MLTTPrelude where

-- This module collects a few basic definitions from the Agda
-- (non-cubical) standard library, to be used not in cubical mode. The
-- corresponding definitions are also in the cubical library, but this
-- is for a small part of the code base which does not use cubical
-- features (used for an experiment in program extraction).

open import Agda.Primitive
open import Agda.Builtin.Sigma public

private
  variable
    ℓ ℓ' : Level

data _⊎_ (A : Set ℓ)(B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B


infix 2 Σ-syntax

Σ-syntax : (A : Set ℓ) → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : (A : Set ℓ)(B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

data ⊥ : Set where

⊥-rec : {A : Set ℓ} → ⊥ → A
⊥-rec ()

¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

infix 6 ¬_

data Dec (A : Set ℓ) : Set ℓ where
  yes : A → Dec A
  no  : ¬ A → Dec A
