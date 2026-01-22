----------------------------------------------------------------------------------------------------
-- Classifiablility of Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Classifiability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Code.Results

open import Abstract.ZerSucLim _<_ _≤_ public

open import PropTrunc

open Properties
 Brw-is-set
 (λ _ _ → <-trunc)
 (λ _ _ → ≤-trunc)
 <-irreflexive
 (λ _ → ≤-refl)
 (λ _ _ _ → ≤-trans)
 (λ _ _ → ≤-antisym)
 <-in-≤
 <∘≤-in-<
 public

zero-is-zero : is-zero zero
zero-is-zero = λ b → ≤-zero

Brw-has-zero : has-zero
Brw-has-zero = zero , zero-is-zero

is-zero→≡zero : {a : Brw} → is-zero a → a ≡ zero
is-zero→≡zero {a} za = x≤zero→x≡zero (za zero)

≡zero→is-zero : {a : Brw} → a ≡ zero → is-zero a
≡zero→is-zero {a} p = subst is-zero (sym p) zero-is-zero

succ-calc-strong-suc : (a : Brw) → (succ a) is-strong-suc-of a
succ-calc-strong-suc a = (≤-refl , (λ x a<x → a<x )) , λ x x<sa → ≤-succ-mono⁻¹ x<sa

succ-is-suc : (a : Brw) → (succ a) is-suc-of a
succ-is-suc a = fst (succ-calc-strong-suc a)

is-suc→≡succ : ∀ {a b} → a is-suc-of b → a ≡ succ b
is-suc→≡succ {a} {b} sa = cong fst (suc-unique b (a , sa) (succ b , fst (succ-calc-strong-suc b)))

limit-is-sup : ∀ f (f↑ : increasing f) → limit f {f↑} is-sup-of f
limit-is-sup f f↑ = (λ i → ≤-cocone-simple f) , λ x → ≤-limiting f {x = x}

is-lim-limit : ∀ f (f↑ : increasing f) → is-lim (limit f {f↑})
is-lim-limit f f↑ = ∣ (f , f↑) , limit-is-sup f f↑ ∣

is-lim→≡limit : ∀ {a f f↑} → a is-lim-of (f , f↑) → a ≡ limit f {f↑}
is-lim→≡limit {a} {f} {f↑} a-is-lim =
 ≤-antisym (snd a-is-lim (limit f {f↑}) (λ n → ≤-cocone-simple f))
           (≤-limiting f {f↑} (λ k → fst a-is-lim k))

≡limit→is-lim : ∀ {a f f↑} → a ≡ limit f {f↑} → a is-lim-of (f , f↑)
≡limit→is-lim {a} {f} {f↑} p = subst (_is-lim-of (f , f↑)) (sym p) (limit-is-sup f f↑)

reduce-to-canonical-limits
 : ∀ {ℓ} → (P : Brw → Type ℓ)
 → ((x : Brw) → isProp (P x))
 → ((f : ℕ → Brw) (f↑ : increasing f) → P (limit f {f↑}))
 → (α : Brw) → is-lim α → P α
reduce-to-canonical-limits P P-is-prop H α = ∥-∥rec (P-is-prop α) H'
 where
  H' : is-Σlim α → P α
  H' ((f , f↑) , α-is-lim) = subst P (sym (is-lim→≡limit α-is-lim)) (H f f↑)

is-sup-increasing→≡limit : ∀ {a f} → (f↑ : increasing f) → a is-sup-of f → a ≡ limit f {f↑}
is-sup-increasing→≡limit {a} {f} f↑ a-is-sup = is-lim→≡limit a-is-sup


Brw-has-limits : has-limits
Brw-has-limits = (λ (f , f↑) → limit f {f↑}) , (λ (f , f↑) → limit-is-sup f f↑)

Brw-has-classification : (a : Brw) → is-classifiable a
Brw-has-classification = Brw-ind (λ a → is-classifiable a) isProp⟨is-classifiable⟩
                                 (inl zero-is-zero)
                                 (λ {a} _ → inr (inl (a , succ-calc-strong-suc a)))
                                 (λ {f} {f↑} _ → inr (inr (is-lim-limit f f↑)))

open ClassifiabilityInduction Brw-has-classification <-is-wellfounded public

Brw-satisfies-classifiability-induction : ∀ ℓ → satisfies-classifiability-induction ℓ
Brw-satisfies-classifiability-induction ℓ = ind {ℓ}

{- Some facts re-stated using is-lim -}

is-lim-cancel-succ-≤ : (y x : Brw) → is-lim y → y ≤ succ x → y ≤ x
is-lim-cancel-succ-≤ y x =
 reduce-to-canonical-limits
  (λ z → z ≤ succ x → z ≤ x)
  (λ _ → isProp→ ≤-trunc)
  (λ f f↑ → lim≤sx→lim≤x f x)
  y

is-lim≰zero : {x : Brw} → is-lim x → x ≤ zero → ⊥
is-lim≰zero {x} =
 reduce-to-canonical-limits
  (λ y → y ≤ zero → ⊥)
  (λ y → isProp→ isProp⊥)
  (λ f f↑ → lim≰zero)
  x
