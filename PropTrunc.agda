{-
We define our own version of the propositional truncation so that we
can use --erased-cubical with it for our benchmarks. In a
non-`erased-cubical` setting, it is exactly like the library
definition.
-}


{-# OPTIONS --erased-cubical --erasure --guardedness --safe #-}
module PropTrunc where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Sigma hiding (∃)
open import Cubical.Data.FinData.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ

data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

∥-∥rec : {P : Type ℓ} → ((x y : P) → (x ≡ y)) → (A → P) → ∥ A ∥ → P
∥-∥rec Pprop f ∣ x ∣ = f x
∥-∥rec Pprop f (squash x y i) = Pprop (∥-∥rec Pprop f x) (∥-∥rec Pprop f y) i

isPropPropTrunc : (x y : ∥ A ∥) → x ≡ y
isPropPropTrunc x y = squash x y

∥-∥map : {A : Type ℓ}{B : Type ℓ'} → (A → B) → ∥ A ∥ → ∥ B ∥
∥-∥map f = ∥-∥rec isPropPropTrunc (λ a → ∣ f a ∣)

∥-∥map2 : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        → (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
∥-∥map2 f = ∥-∥rec (λ g h i x → squash (g x) (h x) i) (λ a → ∥-∥map (f a))

import Cubical.HITs.PropositionalTruncation.Base as Lib

fromLib∥-∥ : Lib.∥ A ∥₁ → ∥ A ∥
fromLib∥-∥ Lib.∣ x ∣₁ = ∣ x ∣
fromLib∥-∥ (Lib.squash₁ x y i) = squash (fromLib∥-∥ x) (fromLib∥-∥ y) i

@0 toLib∥-∥ : ∥ A ∥ → Lib.∥ A ∥₁
toLib∥-∥ ∣ x ∣ = Lib.∣ x ∣₁
toLib∥-∥ (squash x y i) = Lib.squash₁ (toLib∥-∥ x) (toLib∥-∥ y) i

-- Mere existence

∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃ A B = ∥ Σ A B ∥

infix 2 ∃

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
