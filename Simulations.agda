----------------------------------------------------------------------------------------------------
-- Simulations
----------------------------------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --erasure --guardedness --safe #-}

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma

open import PropTrunc

module Simulations {ℓ₁ ℓ₂} (A : Type ℓ₁) (_≼_ : A → A → Type ℓ₂) where

_simulated-by_ : (f g : ℕ → A) → Type _
f simulated-by g = ∀ k → ∥ Σ ℕ (λ n → f k ≼ g n) ∥

_bisimilar-to_ : (f g : ℕ → A) → Type _
f bisimilar-to g = Σ (f simulated-by g) (λ _ → g simulated-by f)


{- Strong (bi)simulations and their properties -}

_strongly-simulated-by_ : (f g : ℕ → A) → Type _
f strongly-simulated-by g = ∀ k → Σ ℕ (λ n → f k ≼ g n)

_strongly-bisimilar-to_ : (f g : ℕ → A) → Type _
f strongly-bisimilar-to g = Σ (f strongly-simulated-by g) (λ _ → g strongly-simulated-by f)

sim-trans : (≼-trans : (a b c : A) → a ≼ b → b ≼ c → a ≼ c) → ∀ {f g h} →
            f strongly-simulated-by g → g strongly-simulated-by h → f strongly-simulated-by h
sim-trans ≼-trans {f} {g} {h} f-g-sim g-h-sim k = n , ≼-trans _ _ _ fk≼gm gm≼hn
  where
  m = fst (f-g-sim k)
  fk≼gm = snd (f-g-sim k)
  n = fst (g-h-sim m)
  gm≼hn = snd (g-h-sim m)

bisim-sym : ∀ {f} {g} → f strongly-bisimilar-to g → g strongly-bisimilar-to f
bisim-sym (f-g-sim , g-f-sim) = (g-f-sim , f-g-sim)

bisim-trans : (≼-trans : (a b c : A) → a ≼ b → b ≼ c → a ≼ c) → ∀ {f g h} →
              f strongly-bisimilar-to g → g strongly-bisimilar-to h → f strongly-bisimilar-to h
bisim-trans ≼-trans (f-g-sim , g-f-sim) (g-h-sim , h-g-sim) =
  sim-trans ≼-trans f-g-sim g-h-sim , sim-trans ≼-trans h-g-sim g-f-sim
