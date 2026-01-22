----------------------------------------------------------------------------------------------------
-- Axioms for ordinals arithmetic
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

module Abstract.Arithmetic
  {i j k}
  {A : Type i}
  (_<_ : A → A → Type j)
  (_≤_ : A → A → Type k)
  where

open import Abstract.ZerSucLim _<_ _≤_


{- Addition -}

is-add : (A → A → A) → Type _
is-add _+_ =
  (∀ a c → is-zero a → c + a ≡ c) ×
  (∀ a b c d → a is-suc-of b → d is-suc-of (c + b) → c + a ≡ d) ×
  (∀ a b c f f↑ → a is-lim-of (f , f↑) → b is-sup-of (λ i → c + f i) → c + a ≡ b)

has-add : Type _
has-add = Σ[ f ∈ (A → A → A) ] is-add f

has-unique-add : Type _
has-unique-add = isContr has-add

isProp⟨is-add⟩ : isSet A → ∀ f → isProp (is-add f)
isProp⟨is-add⟩ isSet⟨A⟩ _ = isProp×2 (isPropΠ3 λ _ _ _ → isSet⟨A⟩ _ _)
                                     (isPropΠ2 λ _ _ → isPropΠ4 λ _ _ _ _ → isSet⟨A⟩ _ _)
                                     (isPropΠ3 λ _ _ _ → isPropΠ4 λ _ _ _ _ → isSet⟨A⟩ _ _)

{- Multiplication -}

module Multiplication
  (add : has-add)
  where

  _+_ : A → A → A
  _+_ = fst add

  is-mul : (A → A → A) → Type _
  is-mul _·_ =
    (∀ a c → is-zero a → c · a ≡ a) ×
    (∀ a b c → a is-suc-of b → c · a ≡ (c · b) + c) ×
    (∀ a b c f f↑ → a is-lim-of (f , f↑) → b is-sup-of (λ i → c · f i) → c · a ≡ b)

  has-mul : Type _
  has-mul = Σ[ f ∈ (A → A → A) ] is-mul f

  has-unique-mul : Type _
  has-unique-mul = isContr has-mul

  isProp⟨is-mul⟩ : isSet A → ∀ f → isProp (is-mul f)
  isProp⟨is-mul⟩ isSet⟨A⟩ _ = isProp×2 (isPropΠ3 λ _ _ _ → isSet⟨A⟩ _ _)
                                       (isPropΠ4 λ _ _ _ _ → isSet⟨A⟩ _ _)
                                       (isPropΠ3 λ _ _ _ → isPropΠ4 λ _ _ _ _ → isSet⟨A⟩ _ _)

{- Exponentiation -}

module Exponentiation
  (add : has-add)
  (mul : Multiplication.has-mul add)
  where

  _·_ : A → A → A
  _·_ = fst mul

  _is-exp-with-base_ : (A → A) → A → Type _
  c^_ is-exp-with-base c =
    (∀ a b   → is-zero a → b is-suc-of a → c^ a ≡ b) ×
    (∀ a b   → a is-suc-of b → c^ a ≡ (c^ b) · c) ×
    (∀ a b f f↑ → a is-lim-of (f , f↑) → ¬ is-zero c → b is-sup-of (λ i → c^ f i) → c^ a ≡ b) ×
    (∀ a   f f↑ → a is-lim-of (f , f↑) →   is-zero c                              → c^ a ≡ c)

  has-exp-with-base : A → Type _
  has-exp-with-base c = Σ[ f ∈ (A → A) ] f is-exp-with-base c

  has-unique-exp-with-base : A → Type _
  has-unique-exp-with-base c = isContr (has-exp-with-base c)

  has-unique-exp : Type _
  has-unique-exp = ∀ c → has-unique-exp-with-base c

  isProp⟨is-exp⟩ : isSet A → ∀ c f → isProp (f is-exp-with-base c)
  isProp⟨is-exp⟩ isSet⟨A⟩ _ _ = isProp×3 (isPropΠ4 λ _ _ _ _ → isSet⟨A⟩ _ _)
                                         (isPropΠ3 λ _ _ _ → isSet⟨A⟩ _ _)
                                         (isPropΠ3 λ _ _ _ → isPropΠ4 λ _ _ _ _ → isSet⟨A⟩ _ _)
                                         (isPropΠ3 λ _ _ _ → isPropΠ2 λ _ _ → isSet⟨A⟩ _ _)

{- Subtraction -}

module Subtraction
  (add : has-add)
  where

  _+_ : A → A → A
  _+_ = fst add

  is-sub : ((b a : A) → a ≤ b → A) → Type _
  is-sub _-_[_] = ∀ b a → (p : a ≤ b) → a + (b - a [ p ]) ≡ b

  has-sub : Type _
  has-sub = Σ[ f ∈ ((b a : A) → a ≤ b → A) ] is-sub f

  has-unique-sub : Type _
  has-unique-sub = isContr has-sub

  isProp⟨is-sub⟩ : isSet A → ∀ f → isProp (is-sub f)
  isProp⟨is-sub⟩ isSet⟨A⟩ _ = isPropΠ3 λ _ _ _ → isSet⟨A⟩ _ _
