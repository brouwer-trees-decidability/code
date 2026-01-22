----------------------------------------------------------------------------------------------------
-- A positive formulation of "no infinitely descending sequences"
----------------------------------------------------------------------------------------------------

{- We recall and generalise the proof that wellfounded orders have no
   infinitely descending sequences, formulated positively, from

     Threee quivalent ordinal notation systems in cubical agda.
-}

{-# OPTIONS --cubical --erasure --guardedness --safe #-}

module InfinitelyDescendingSequences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order  as ℕ
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open BinaryRelation renaming (isTrans to isTransitive ; isRefl to isReflexive)
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)


open import General-Properties
import Abstract.ZerSucLim as Abstract

module _
  (A : Type)
  (isSet⟨A⟩ : isSet A)
  (_<_ : A → A → Type)
  (_≤_ : A → A → Type)
  (isProp⟨<⟩ : isPropValued _<_)
  (isProp⟨≤⟩ : isPropValued _≤_)
  (<-irrefl : isIrrefl _<_)
  (≤-refl : isReflexive _≤_)
  (≤-trans : isTransitive _≤_)
  (≤-antisym : isAntisym _≤_)
  (<-in-≤ : {a b : A} → a < b → a ≤ b)
  (<∘≤-in-< : {a b c : A} → a < b → b ≤ c → a < c)
  -- Additional assumption: there is a zero
  (𝟎 : A)
  (𝟎-is-zero : Abstract.is-zero _<_ _≤_ 𝟎)
  where

  open Abstract _<_ _≤_
  open Abstract.Properties _<_ _≤_ isSet⟨A⟩ isProp⟨<⟩ isProp⟨≤⟩ <-irrefl ≤-refl ≤-trans ≤-antisym <-in-≤ <∘≤-in-<

  -- A pseudo-descending sequence is strictly descending until it hits 0
  pseudo-descending : (ℕ → A) → Type
  pseudo-descending f =
    ∀ i → (f (suc i) < f i)  ⊎ ((f i ≡ 𝟎) × (f (suc i) ≡ 𝟎))
  eventually-zero : (ℕ → A) → Type₀
  eventually-zero f = Σ[ n ∈  ℕ ] (∀ i → n ℕ.≤ i → f i ≡ 𝟎)

  zeroPoint : ∀ {f} → pseudo-descending f → ∀ {i} → f i ≡ 𝟎 → ∀ j → i  ℕ.≤ j → f j ≡ 𝟎
  zeroPoint {f} df fi=0 zero j≤0 = subst (λ z → f z ≡ 𝟎) (≤0→≡0 j≤0) fi=0
  zeroPoint {f} df fi=0 (suc j) (zero , i=sj) = subst (λ z → f z ≡ 𝟎) i=sj fi=0
  zeroPoint {f} df {i} fi=0 (suc j) (suc n , sn+1=sj) with df i
  ... | inl fsi<fi = ⊥.rec (≮-zero 𝟎-is-zero (f (suc i)) (subst (f (suc i) <_) fi=0 fsi<fi))
  ... | inr (_ , fsi=0) = zeroPoint (df ∘ suc) fsi=0 j ((n , injSuc sn+1=sj))


  nonzeroPoint : ∀ {f} → pseudo-descending f → ∀ {i} → 𝟎 < f i → f (suc i) < f i
  nonzeroPoint df fi>0 with df _
  nonzeroPoint df fi>0 | inl fi+1<fi    = fi+1<fi
  nonzeroPoint df fi>0 | inr (fi=0 , _) = ⊥.elim (<-irrefl 𝟎 (subst (𝟎 <_) fi=0 fi>0))

  eventually-zero-cons : ∀ f → eventually-zero (f ∘ suc) → eventually-zero f
  eventually-zero-cons f (n , p) = suc n , p' where
   p' : (i : ℕ) → suc n ℕ.≤ i  → f i ≡ 𝟎
   p' zero sn≤0 = ⊥.rec (snotz (≤0→≡0 sn≤0))
   p' (suc i) (m , q) = p i ((m , injSuc (sym (+-suc m n) ∙ q)))

  -- If we can decide if an element is 𝟎, then all pseudo-descending sequences are eventually zero.

  PD2EZ : ((b : A) → (b ≡ 𝟎) ⊎ (𝟎 < b)) -> isWellFounded _<_ → ∀ f → pseudo-descending f → eventually-zero f
  PD2EZ dec-≡0 wf f df = WFI.induction wf {P = P} step (f 0) f df refl where
    P : A → Type₀
    P a = ∀ f → pseudo-descending f → f 0 ≡ a → eventually-zero f
    step : ∀ x → (∀ y → y < x → P y) → P x
    step x h f df f0=x with dec-≡0 (f 0)
    ... | inr f0>0 = goal where
      f1<x : f 1 < x
      f1<x = subst (f 1 <_) f0=x (nonzeroPoint df f0>0)
      ezfs : eventually-zero (f ∘ suc)
      ezfs = h (f 1) f1<x (f ∘ suc) (df ∘ suc) refl
      goal : eventually-zero f
      goal = eventually-zero-cons f ezfs
    ... | inl f0=0 = goal where
      fi=0 : ∀ i → f i ≡ 𝟎
      fi=0 i = zeroPoint df f0=0 i zero-≤
      goal : eventually-zero f
      goal = 0 , λ i _ → fi=0 i

  -- Note: this straightforwardly implies
  --    `Wellfounded _<_ → ∀ f → strictly-descending f → ⊥`
  -- but this can also be proven without assuming `_≡ 𝟎` is decidable,
  -- see General-Properties.
