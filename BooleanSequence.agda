----------------------------------------------------------------------------------------------------
-- Some functions on boolean-value sequences
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --guardedness --erasure #-}

module BooleanSequence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Bool renaming (true to tt; false to ff) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (_≟_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.Relation.Binary

open import PropTrunc

--
-- some-true f n = tt  iff  f i = tt for some i ≤ n
--
some-true : (ℕ → Bool) → ℕ → Bool
some-true f  0      = f 0
some-true f (suc n) = if (some-true f n) then tt else f(suc n)

some-true-spec-tt : (f : ℕ → Bool)
  → (n : ℕ) → f n ≡ tt
  → some-true f n ≡ tt
some-true-spec-tt f 0 f0≡tt = f0≡tt
some-true-spec-tt f (suc n) fn+1≡tt with some-true f n ≟ tt
... | yes p = goal
 where
  goal : some-true f (suc n) ≡ tt
  goal = cong (if_then tt else f(suc n)) p
... | no ¬p = goal
 where
  p : some-true f n ≡ ff
  p = ¬true→false _ ¬p
  claim : some-true f (suc n) ≡ f (suc n)
  claim = cong (if_then tt else f(suc n)) p
  goal : some-true f (suc n) ≡ tt
  goal = claim ∙ fn+1≡tt

some-true-case-tt : (f : ℕ → Bool)
  → (n : ℕ) → some-true f n ≡ tt
  → Σ[ i ∈ ℕ ] (i ≤ n) × (f i ≡ tt)
some-true-case-tt f 0 p = 0 , ≤-refl , p
some-true-case-tt f (suc n) p with some-true f n ≟ tt
... | yes q = fst IH , ≤-suc (fst (snd IH)) , snd (snd IH)
 where
  IH : Σ[ i ∈ ℕ ] (i ≤ n) × (f i ≡ tt)
  IH = some-true-case-tt f n q
... | no ¬q = suc n , ≤-refl , fn+1≡tt
 where
  q : some-true f n ≡ ff
  q = ¬true→false _ ¬q
  claim : some-true f (suc n) ≡ f (suc n)
  claim = cong (if_then tt else f(suc n)) q
  fn+1≡tt : f (suc n) ≡ tt
  fn+1≡tt = sym claim ∙ p

some-true-spec-ff : (f : ℕ → Bool)
  → (n : ℕ) → (∀ i → i ≤ n → f i ≡ ff)
  → some-true f n ≡ ff
some-true-spec-ff f 0 p = p 0 ≤-refl
some-true-spec-ff f (suc n) p = goal
 where
  q : ∀ i → i ≤ n → f i ≡ ff
  q i i≤n = p i (≤-suc i≤n)
  IH : some-true f n ≡ ff
  IH = some-true-spec-ff f n q
  claim₀ : some-true f (suc n) ≡ f (suc n)
  claim₀ = cong (if_then tt else f(suc n)) IH
  claim₁ : f (suc n) ≡ ff
  claim₁ = p (suc n) ≤-refl
  goal : some-true f (suc n) ≡ ff
  goal = claim₀ ∙ claim₁

some-true-case-ff : (f : ℕ → Bool)
  → (n : ℕ) → some-true f n ≡ ff
  → ∀ i → i ≤ n → f i ≡ ff
some-true-case-ff f 0 p i i≤0 = subst (λ x → f x ≡ ff) (sym (≤0→≡0 i≤0)) p
some-true-case-ff f (suc n) p with some-true f n ≟ tt
some-true-case-ff f (suc n) p | yes q = ⊥.rec (true≢false tt≡ff)
 where
  tt≡ff : tt ≡ ff
  tt≡ff = sym (cong (if_then tt else f(suc n)) q) ∙ p
some-true-case-ff f (suc n) p | no ¬q = goal
 where
  q : some-true f n ≡ ff
  q = ¬true→false _ ¬q
  IH : ∀ i → i ≤ n → f i ≡ ff
  IH = some-true-case-ff f n q
  fn+1≡ff : f (suc n) ≡ ff
  fn+1≡ff = sym (cong (if_then tt else f(suc n)) q) ∙ p
  goal : ∀ i → i ≤ suc n → f i ≡ ff
  goal i (0 , i≡n+1) = subst (λ x → f x ≡ ff) (sym i≡n+1) fn+1≡ff
  goal i (suc k , k+i+1≡n+1) = IH i (k , injSuc k+i+1≡n+1)


--
-- least-true f i = tt  iff  i is the least such that f i = tt
--
least-index-true : (ℕ → Bool) → ℕ → Bool
least-index-true f  0      = f 0
least-index-true f (suc n) = if (some-true f n) then ff else f(suc n)

least-index-true-case-tt : (f : ℕ → Bool)
  → (n : ℕ) → least-index-true f n ≡ tt
  → ∀ i → i < n → f i ≡ ff
least-index-true-case-tt f 0 p i i<0 = ⊥.rec (¬-<-zero i<0)
least-index-true-case-tt f (suc n) p with some-true f n ≟ tt
least-index-true-case-tt f (suc n) p | yes q = ⊥.rec (true≢false (sym p ∙ claim))
 where
  claim : least-index-true f (suc n) ≡ ff
  claim = cong (if_then ff else f(suc n)) q
least-index-true-case-tt f (suc n) p | no ¬q = goal
 where
  q : some-true f n ≡ ff
  q = ¬true→false _ ¬q
  claim : ∀ i → i ≤ n → f i ≡ ff
  claim = some-true-case-ff f n q
  goal : ∀ i → i < suc n → f i ≡ ff
  goal i i<n+1 = claim i (pred-≤-pred i<n+1)

least-index-true-is-true : (f : ℕ → Bool)
  → (n : ℕ) → least-index-true f n ≡ tt
  → f n ≡ tt
least-index-true-is-true f zero p = p
least-index-true-is-true f (suc n) p  with some-true f n
... | ff = p
... | tt = ⊥.rec (false≢true p)

least-index-true-spec-tt' : (f : ℕ → Bool)
  → (n : ℕ) → some-true f n ≡ tt
  → Σ[ i ∈ ℕ ] (i ≤ n) × (least-index-true f i ≡ tt)
least-index-true-spec-tt' f 0 p = 0 , ≤-refl , p
least-index-true-spec-tt' f (suc n) p with some-true f n ≟ tt
... | yes q = fst IH , ≤-suc (fst (snd IH)) , snd (snd IH)
 where
  IH : Σ[ i ∈ ℕ ] (i ≤ n) × (least-index-true f i ≡ tt)
  IH = least-index-true-spec-tt' f n q
... | no ¬q = suc n , ≤-refl , claim₃
 where
  q : some-true f n ≡ ff
  q = ¬true→false _ ¬q
  claim₀ : least-index-true f (suc n) ≡ f (suc n)
  claim₀ = cong (if_then ff else f(suc n)) q
  claim₁ : some-true f (suc n) ≡ f(suc n)
  claim₁ = cong (if_then tt else f(suc n)) q
  claim₂ : f (suc n) ≡ tt
  claim₂ = sym claim₁ ∙ p
  claim₃ : least-index-true f (suc n) ≡ tt
  claim₃ = claim₀ ∙ claim₂

least-index-true-spec-tt : (f : ℕ → Bool)
  → (n : ℕ) → f n ≡ tt
  → Σ[ i ∈ ℕ ] (i ≤ n) × (least-index-true f i ≡ tt)
least-index-true-spec-tt f n fn≡tt =
  least-index-true-spec-tt' f n (some-true-spec-tt f n fn≡tt)

least-index-true-spec-ff : (f : ℕ → Bool)
  → (n : ℕ) → (∀ i → i ≤ n → f i ≡ ff)
  → least-index-true f n ≡ ff
least-index-true-spec-ff f 0 p = p 0 ≤-refl
least-index-true-spec-ff f (suc n) p = goal
 where
  q : some-true f n ≡ ff
  q = some-true-spec-ff f n (λ i i≤n → p i (≤-suc i≤n))
  claim₀ : least-index-true f (suc n) ≡ f (suc n)
  claim₀ = cong (if_then ff else f(suc n)) q
  claim₁ : f (suc n) ≡ ff
  claim₁ = p (suc n) ≤-refl
  goal : least-index-true f (suc n) ≡ ff
  goal = claim₀ ∙ claim₁


----------------
-- It is decidable to get true in a finite segment of a countable sequence.
dec-true-below : (n : ℕ) → (s : ℕ → Bool) → Dec (Σ ℕ (λ k  → (k ≤ n) × (s k ≡ tt)))
dec-true-below zero s with s zero ≟ tt
... | yes z =  yes (zero , zero-≤ , z)
... | no  z' = no h
 where
  h : ¬ Σ ℕ (λ k  → (k ≤ zero) × (s k ≡ tt))
  h (k , l , p) = z' (subst (λ - → s - ≡ tt) (≤0→≡0 l) p)
dec-true-below (suc n) s with dec-true-below n s
... | yes (k , l , p)  = yes (k , ≤-suc l , p)
... | no  z' with s (suc n) ≟ tt
... | yes y = yes (suc n , ≤-refl , y)
... | no  y' = no h
 where
  h : ¬ Σ ℕ (λ k  → ((k ≤ suc n) × (s k ≡ tt)))
  h (k , l , p) = z' (k , ≤-suc-≢ l h' , p)
   where
    h' : ¬ k ≡ suc n
    h' e = y' (subst (λ - → s - ≡ tt) e p)

dec-∃-true-below : (n : ℕ) → (s : ℕ → Bool) → Dec ∥ Σ ℕ (λ k  → (k ≤ n) × (s k ≡ tt)) ∥
dec-∃-true-below n s with dec-true-below n s
... | yes v = yes ∣ v ∣
... | no  v' = no (λ x → ∥-∥rec ⊥.elim v' x)
