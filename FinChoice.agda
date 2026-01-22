{-
We define our own version of the propositional truncation so that we
can use --erased-cubical with it for our benchmarks. In a
non-`erased-cubical` setting, it is exactly like the library
definition.
-}


{-# OPTIONS --cubical --erasure --guardedness --safe #-}
module FinChoice where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.FinData.Base
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma



open import PropTrunc

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ

∥-∥recFin : {m : ℕ} {P : Fin m → Type ℓ}
            {B : Type ℓ'} (isPropB : isProp B)
            → ((∀ i → P i) → B)
            → ((∀ i → ∥ P i ∥) → B)
∥-∥recFin {m = zero} _ untruncHyp _ = untruncHyp (λ ())
∥-∥recFin {m = suc m} {P = P} {B = B} isPropB untruncHyp truncFam =
  ∥-∥rec (isProp→ isPropB) δ (truncFam zero) (truncFam ∘ suc)
  where
   δ : P zero → (∀ i → ∥ P (suc i) ∥) → B
   δ p₀ = ∥-∥recFin isPropB
                    (λ pₛ → untruncHyp (λ { zero → p₀ ; (suc i) → pₛ i }))

∥∥-×→ : {A : Type ℓ} {B : Type ℓ'} → ∥ A ∥ × ∥ B ∥ → ∥ A × B ∥
∥∥-×→  = uncurry (∥-∥rec (isProp→ isPropPropTrunc)
                         (λ a → ∥-∥rec isPropPropTrunc (λ b → ∣ a , b ∣)))

Finite-Choice : {A : (i : ℕ) → Type ℓ} → (n : ℕ)
              → (∀ (i : ℕ) → i < n → ∥ A i ∥)
              → ∥ ((i : ℕ) → i < n →  A i) ∥
Finite-Choice zero f = ∣ (λ i p → ⊥.rec (¬-<-zero p)) ∣
Finite-Choice {ℓ} {A} (suc zero) f = ∥-∥map [2] (f zero ≤-refl)
  where
   [2] : A 0 → (i : ℕ) → i < 1 → A i
   [2] a0 zero p = a0
   [2] a0 (suc i) p = ⊥.rec (¬-<-zero (pred-≤-pred p))
Finite-Choice {ℓ} {A} (suc m@(suc n)) f =
 ∥-∥map δ (∥∥-×→ (Finite-Choice m (λ i q → f i (<-trans q <-suc)) , f m <-suc))
  where
   δ : ((i : ℕ) → i < suc n → A i) × A (suc n) → (j : ℕ) → j < suc (suc n) → A j
   δ (f , asn) zero p = f zero (suc-≤-suc zero-≤)
   δ (f , asn) j@(suc i) p with i ≟ n
   ... | lt v = f j (n ∸ j , ρ (suc n) (suc j) (suc-≤-suc v))
    where
     ρ : ∀ (n m : ℕ) → (m ≤ n) →  n ∸ m + m ≡ n
     ρ zero zero p = refl
     ρ zero (suc m) p = ⊥.rec (¬-<-zero p)
     ρ (suc n) zero p = cong suc (+-zero n)
     ρ (suc n) (suc m) p = +-suc (n ∸ m) m ∙ cong suc (ρ n m (pred-≤-pred p))
   ... | eq u = transport (cong (λ j → A (suc j)) (sym u)) asn
   ... | gt z = ⊥.rec (¬m<m (≤-trans z (pred-≤-pred (pred-≤-pred p))))

--------------------------------------------------------------
-- Weakly constant map has a factorization along truncation:

module _ (Bset : isSet B) where
 LBset' : isSet' B
 LBset' = isSet→isSet' Bset

 Lrec→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥ → B
 Lhelper  : (f : A → B) (kf : 2-Constant f) → (t u : ∥ A ∥)
          → Lrec→Set f kf t ≡ Lrec→Set f kf u

 Lrec→Set f kf ∣ x ∣ = f x
 Lrec→Set f kf (squash t u i) = Lhelper f kf t u i

 Lhelper f kf ∣ x ∣ ∣ y ∣ = kf x y
 Lhelper f kf (squash t u i) v
    = LBset' (Lhelper f kf t v) (Lhelper f kf u v) (Lhelper f kf t u) refl i
 Lhelper f kf t (squash u v i)
    = LBset' (Lhelper f kf t u) (Lhelper f kf t v) refl (Lhelper f kf u v) i

Weakly-Constant : {A : Type ℓ} {B : Type ℓ'} (f : A → B)
                → Type (ℓ-max ℓ ℓ')
Weakly-Constant {ℓ} {ℓ'} {A} {B} f = (x y : A) → f x ≡ f y

WC-Factorisation : {A : Type ℓ} {B : Type ℓ'} → isSet B → (f : A → B)
                 → Weakly-Constant f
                 → Σ (∥ A ∥ → B) (λ g → (∀ (x : A) → (f x ≡ g ∣ x ∣)))
WC-Factorisation issetB f wCons = Lrec→Set issetB f wCons , λ x → wCons x x
