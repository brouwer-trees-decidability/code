{-# OPTIONS --cubical --erasure  --guardedness --lossy-unification #-}
module BrouwerTree.OrdinalDecidability.QuantificationCut where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; +-zero; +-suc) renaming (_+_ to _N+_)
import Cubical.Data.Nat.Order as N
import Cubical.Data.Nat.Properties as N
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)

open import Iff
open import Bool
open import PropTrunc
open import FinChoice

open import BrouwerTree.Everything

open import BrouwerTree.OrdinalDecidability.Basic
open import BrouwerTree.OrdinalDecidability.GeneralProperties
open import BrouwerTree.OrdinalDecidability.QuantificationConstruction
open import BrouwerTree.OrdinalDecidability.QuantificationLemmas

private
 variable
  ℓ ℓ' : Level

cut : (P : ℕ → Type ℓ) → ℕ → (ℕ → Type ℓ)
cut P n i =  P (n N+ i)

isPropCut : (P : ℕ → Type ℓ)
          → ((n : ℕ) → isProp (P n))
          → (n m : ℕ) → isProp (cut P n m)
isPropCut P isProp⟨P⟩ n m = isProp⟨P⟩ (n N+ m)

semidecCut : (P : ℕ → Type ℓ)
           → ((n : ℕ) → semi-dec (P n))
           → (n m : ℕ) → semi-dec (cut P n m)
semidecCut P σ n m = σ (n N+ m)

module _
       (P : ℕ → Type ℓ)
      where
 open CharacteristicOrdinal P
 open CharacteristicOrdinal-Construction₁
 open CharacteristicOrdinal-Construction₂

 normal-seq-sum-eq-lemma
  : {n m : ℕ}
  → (p : n ≡ m)
  → (σ : P semi-dec-str-up-to n)
  → (τ : P semi-dec-str-up-to m)
  → ((i : ℕ) (l : i N.< n) → σ i l ≡ τ i (subst (i N.<_) p l))
  → (k : ℕ) → normal-seq-sum n σ k ≡ normal-seq-sum m τ k
 normal-seq-sum-eq-lemma {n} = J Q Q-refl
  where
   Q : (m : ℕ) → n ≡ m → Type ℓ
   Q m p = (σ : P semi-dec-str-up-to n)
           → (τ : P semi-dec-str-up-to m)
           → ((i : ℕ) (l : i N.< n) → σ i l ≡ τ i (subst (i N.<_) p l))
           → (k : ℕ) → normal-seq-sum n σ k ≡ normal-seq-sum m τ k
   Q-refl : Q n refl
   Q-refl σ τ H k = cong (λ - → normal-seq-sum n - k) e
    where
     e : σ ≡ τ
     e = funExt (λ i →
          funExt (λ l →
           σ i l                       ≡⟨ H i l ⟩
           τ i (subst (i N.<_) refl l) ≡⟨ cong (τ i) (substRefl l) ⟩
           τ i l                       ∎))

 ω-sequence-eq-lemma
  : {n m : ℕ}
  → (p : n ≡ m)
  → (σ : P semi-dec-str-up-to n)
  → (τ : P semi-dec-str-up-to m)
  → ((i : ℕ) (l : i N.< n) → σ i l ≡ τ i (subst (i N.<_) p l))
  → (k : ℕ) → ω-sequence n σ k ≡ ω-sequence m τ k
 ω-sequence-eq-lemma {n} = J Q Q-refl
  where
  Q : (m : ℕ) → n ≡ m → Type ℓ
  Q m p = (σ : P semi-dec-str-up-to n)
          → (τ : P semi-dec-str-up-to m)
          → ((i : ℕ) (l : i N.< n) → σ i l ≡ τ i (subst (i N.<_) p l))
          → (k : ℕ) → ω-sequence n σ k ≡ ω-sequence m τ k
  Q-refl : Q n refl
  Q-refl σ τ H k = cong (λ - → ω-sequence n - k) e
   where
    e : σ ≡ τ
    e = funExt (λ i →
         funExt (λ l →
          σ i l                       ≡⟨ H i l ⟩
          τ i (subst (i N.<_) refl l) ≡⟨ cong (τ i) (substRefl l) ⟩
          τ i l                       ∎))

 normal-seq-eq-lemma
  : {n m u : ℕ}
  → (p : n ≡ m)
  → (u<n : u N.< n)
  → (u<m : u N.< m)
  → (σ : P semi-dec-str-up-to n)
  → (τ : P semi-dec-str-up-to m)
  → ((i : ℕ) (l : i N.< n) → σ i l ≡ τ i (subst (i N.<_) p l))
  → (k : ℕ) → normal-seq n σ u u<n k ≡ normal-seq m τ u u<m k
 normal-seq-eq-lemma {n} {u = u} p = J Q Q-refl p
  where
   Q : (m : ℕ) → n ≡ m → Type ℓ
   Q m p =  (u<n : u N.< n)  → (u<m : u N.< m)
           → (σ : P semi-dec-str-up-to n)
           → (τ : P semi-dec-str-up-to m)
           → ((i : ℕ) (l : i N.< n) → σ i l ≡ τ i (subst (i N.<_) p l))
           → (k : ℕ) → normal-seq n σ u u<n k ≡ normal-seq m τ u u<m k
   Q-refl : Q n refl
   Q-refl u<n u<m σ τ H k =
    cong (λ - → normal-seq n σ u - k ) c ∙ cong (λ - → normal-seq n - u u<m k) e
     where
      c : u<n ≡ u<m
      c = N.isProp≤ u<n u<m
      e : σ ≡ τ
      e = funExt (λ i →
           funExt (λ l →
            σ i l                       ≡⟨ H i l ⟩
            τ i (subst (i N.<_) refl l) ≡⟨ cong (τ i) (substRefl l) ⟩
            τ i l ∎))

module _ (P : ℕ → Type ℓ) where
 open CharacteristicOrdinal
 open CharacteristicOrdinal-Construction₁
 open CharacteristicOrdinal-Construction₂

 cut-split-sequence
  : (n k m : ℕ)
  → (σ : P semi-dec-str-up-to (n N+ k))
  → let σₙ = (λ i p → σ i (N.≤-trans p N.≤SumLeft))
        σₖ = (λ i p → σ (n N+ i) (N.<-k+ p))
  in ω-sequence P (n N+ k) σ m ≤ ω-sequence P n σₙ m + ω-sequence (cut P n) k σₖ m
 cut-split-sequence n zero m σ = subst Q ([1] m) (x+-increasing _)
  where
   σₙ = (λ i p → σ i (N.≤-trans p N.≤SumLeft))
   σₖ = (λ i p → σ (n N+ i) (N.<-k+ p))

   Q = λ z → ω-sequence P (n N+ zero) σ m ≤ z + ω-sequence (cut P n) zero σₖ m
   [1] : (m : ℕ) → ω-sequence P (n N+ zero) σ m ≡ ω-sequence P n σₙ m
   [1] = ω-sequence-eq-lemma P
           (+-zero n)
           σ
           (λ i p → σ i (N.≤-trans p N.≤SumLeft))
           (λ i l  → cong (σ i) (N.isProp≤ l _))
 cut-split-sequence n (suc k) m σ =
  ω-sequence P (n N+ suc k) σ m
    ≤⟨ +x-mono (ι m) [4] ⟩
  (Ψ-n-+m + Ψ-cutn-sk) + ι m
    ≤⟨ ≤-refl-≡ (sym (+-assoc (ι m))) ⟩
  ω-sequence P n σₙ m + ω-sequence (cut P n) (suc k) σₖ m
    ≤∎
   where
    σₙ = (λ i p → σ i (N.≤-trans p N.≤SumLeft))
    σₖ = (λ i p → σ (n N+ i) (N.<-k+ p))

    σ' : P semi-dec-str-up-to (n N+ k)
    σ' =  (λ i p → σ i (N.≤-trans p (N.≤-k+ N.≤-sucℕ)))
    σ'ₙ = (λ i p → σ' i (N.≤-trans p N.≤SumLeft))
    σ'ₖ = (λ i p → σ' (n N+ i) (N.<-k+ p))

    σ'ₙ-σₙ-agrees : σ'ₙ ≡ σₙ
    σ'ₙ-σₙ-agrees = funExt (λ i  → funExt (λ p → cong (σ i) (N.isProp≤ _ _)))

    ρ : (i : ℕ) → i N.< suc (n N+ k) → semi-dec-str (P i)
    ρ i p = σ i (subst (i N.<_) (sym (+-suc n k)) p)

    Ψ-n+k+1 = ω · ι (normal-seq-sum P (n N+ suc k) σ m)
    Ψ-n-+m = ω · ι (normal-seq-sum P n σₙ m) + ι m
    Ψ-cutn-sk = ω · ι (normal-seq-sum (cut P n) (suc k) σₖ m)
    Ψ-n+k = ω · ι (normal-seq-sum P (n N+ k) σ'  m)
    Ψ-cutn-k = ω · ι (normal-seq-sum (cut P n) k σ'ₖ m)

    β = Bool→Nat (normal-seq P (n N+ suc k) σ (n N+ k) (N.<-k+ N.<-suc) m)

    IH : Ψ-n+k + ι m ≤ Ψ-n-+m + (Ψ-cutn-k + ι m)
    IH = subst (λ z → Ψ-n+k + ι m ≤  ω-sequence P n z m + ( Ψ-cutn-k + ι m) )
               σ'ₙ-σₙ-agrees
               (cut-split-sequence n k m σ')

    [1] :  Ψ-n+k ≤ Ψ-n-+m + Ψ-cutn-k
    [1] = finite-cancellation-lemma m IH
     where
      finite-cancellation-lemma : {u v z : ℕ} → (m : ℕ)
                                → ω · ι u + ι m ≤ (ω · ι v + ι m) + (ω · ι z + ι m)
                                → ω · ι u ≤ (ω · ι v + ι m) + ω · ι z
      finite-cancellation-lemma {zero} zero h = h
      finite-cancellation-lemma {zero} (suc m) h = ≤-zero
      finite-cancellation-lemma {suc u} m h =
       finite-right-cancellation _ _ (ω·sk-islim u) m (≤-trans h
                                                               (≤-refl-≡ (+-assoc (ι m))))

    [2] : Ψ-n+k+1 ≡ Ψ-n+k + ω · ι β
    [2] = ω·k-split
           (normal-seq-sum P (n N+ suc k) σ m)
           (normal-seq-sum P (n N+ k) σ' m)
           β
           (normal-seq-sum P (n N+ suc k) σ m
              ≡⟨ [2]₀ ⟩
            normal-seq-sum P (suc (n N+ k)) ρ m
              ≡⟨ [2]₁ ⟩
            normal-seq-sum P (n N+ k) (semi-dec-str-restricted P N.<-suc ρ) m
             N+ Bool→Nat (normal-seq P (suc (n N+ k)) ρ (n N+ k) N.<-suc m)
              ≡⟨ cong₂ _N+_ [2]₂ [2]₃ ⟩
            normal-seq-sum P (n N+ k) σ' m N+ β ∎)
     where
      [2]₀ = sym (normal-seq-sum-eq-lemma P _ ρ σ (λ i l → refl) m)
      [2]₁ = normal-seq-sum-suc P {n = n N+ k}  ρ m
      [2]₂ = cong (λ z → normal-seq-sum P (n N+ k) z m)
                  (funExt (λ i → funExt (λ p → cong (σ i) (N.isProp≤ _ _))))
      [2]₃ = cong Bool→Nat (normal-seq-eq-lemma P _ _ _ ρ σ (λ i l → refl) m)

    [3] : Ψ-cutn-sk ≡ Ψ-cutn-k + ω · ι β
    [3] = ω·k-split
           (normal-seq-sum (cut P n) (suc k) σₖ m)
           (normal-seq-sum (cut P n) k  σ'ₖ m)
           β
           (normal-seq-sum (cut P n) (suc k) σₖ m
              ≡⟨ [3]₀ ⟩
            normal-seq-sum (cut P n) k (semi-dec-str-restricted (cut P n) N.<-suc σₖ) m N+ β
              ≡⟨ cong (_N+ β) [3]₁ ⟩
            normal-seq-sum (cut P n) k σ'ₖ m N+ β ∎)
      where
         [3]₀ = normal-seq-sum-suc (cut P n) σₖ m
         [3]₁ = cong (λ z → normal-seq-sum (cut P n) k z m)
                     (funExt (λ i → funExt (λ p → cong (σ (n N+ i)) (N.isProp≤ _ _))))

    [4] : Ψ-n+k+1 ≤ Ψ-n-+m + Ψ-cutn-sk
    [4] = subst2 _≤_ (sym [2]) (cong (Ψ-n-+m +_) (sym [3]))
                     (≤-trans (+x-mono (ω · ι β) [1])
                              (≤-refl-≡ (sym (+-assoc (ω · ι β)))))

 cut-split-lemma
  : (n k : ℕ)
  → (σ : P semi-dec-str-up-to (n N+ k))
  → semi-dec-limit-ordinal P (n N+ k) σ ≤
    semi-dec-limit-ordinal P n (semi-dec-str-restricted-≤ P N.≤SumLeft σ)
     + semi-dec-limit-ordinal (cut P n) k (λ i p → σ (n N+ i) (N.<-k+ p))
 cut-split-lemma n k σ =
  simulation→≤ (λ m → m , ≤-trans (cut-split-sequence n k m σ)
                                  (+-mono (≤-cocone _ ≤-refl) ≤-refl))

 cut-complement-semi-dec-limit-ordinal
  : (n k : ℕ)
  → (σ : P semi-dec-str-up-to (n N+ k))
  → semi-dec-limit-ordinal P k (semi-dec-str-restricted-≤ P N.≤SumRight σ) ≤
    semi-dec-limit-ordinal P n (semi-dec-str-restricted-≤ P N.≤SumLeft σ)
     + semi-dec-limit-ordinal (cut P n) k (λ i p → σ (n N+ i) (N.<-k+ p))
 cut-complement-semi-dec-limit-ordinal n k σ =
  ≤-trans (semi-dec-limit-ordinal-increasing' P n k σ )
          (cut-split-lemma n k σ)

 cut-complement-characteristic-ordinal-up-to
  : (σ : (n : ℕ) → semi-dec (P n))
  → (n k : ℕ)
  → (P characteristic-ordinal-up-to k) (semi-dec-restrict-to k σ) ≤
    (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
      + (cut P n characteristic-ordinal-up-to k) (semi-dec-restrict-to k (λ i → σ (n N+ i)))
 cut-complement-characteristic-ordinal-up-to σ n k = ∥-∥rec ≤-trunc [1] |n+kData|
   where
      |n+kData| : ∥ (∀ (i : ℕ) → (((i<n : i N.< (n N+ k)) → (semi-dec-str (P i))))) ∥
      |n+kData| = Finite-Choice (n N+ k) (λ i p → σ i)
      [1] :  P semi-dec-str-up-to (n N+ k)
          →  (P characteristic-ordinal-up-to k) (semi-dec-restrict-to k σ) ≤
             (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
               + (cut P n characteristic-ordinal-up-to k) (semi-dec-restrict-to k (λ i → σ (n N+ i)))
      [1] ρ =
       subst2 _≤_
        (characteristic-ordinal-up-to-compatible P k _ _)
        (cong₂ _+_
          (characteristic-ordinal-up-to-compatible P n _ _)
          (characteristic-ordinal-up-to-compatible (cut P n) k _ _))
        (cut-complement-semi-dec-limit-ordinal n k ρ)

 cut-complement : (σ : (n : ℕ) → semi-dec (P n)) →
                  (n : ℕ) →
                   characteristic-ordinal P σ ≤
                   (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ) +
                   characteristic-ordinal (cut P n) λ i → σ (n N+ i)
 cut-complement σ n =
  simulation→≤ (λ k → k , subst (_ ≤_) (sym (+-assoc (ι k))) ([1] k))
   where
    α : (k : ℕ) → Brw
    α k = (P characteristic-ordinal-up-to k) (semi-dec-restrict-to k σ)
    β : (k : ℕ) → Brw
    β k = (cut P n characteristic-ordinal-up-to k) (semi-dec-restrict-to k (λ i → σ (n N+ i)))
    [1] : (k : ℕ) → α k + ι k ≤ (α n + β k) + ι k
    [1] k = +x-mono (ι k) (cut-complement-characteristic-ordinal-up-to σ n k)

 cut-preserves-characteristic-ordinal-≥ω²
  : (σ : (n : ℕ) → semi-dec (P n))
  → (n : ℕ)
  → ω · ω  ≤  characteristic-ordinal P σ
  → ω · ω  ≤  characteristic-ordinal (cut P n) (semidecCut P σ n)
 cut-preserves-characteristic-ordinal-≥ω² σ n H =
  subst (_≤ characteristic-ordinal (cut P n) (semidecCut P σ n)) ω^ι2≡ω² [2]
   where
     H' : ω ^ ι 2 ≤  characteristic-ordinal P σ
     H' = subst (_≤  characteristic-ordinal P σ) (sym ω^ι2≡ω²) H
     [1] :  ω · ι (suc n) ≡ (ω ^ ι 1) · ι (suc n)
     [1] = cong (_· ι (suc n)) (sym ω^one≡ω)
     [2] :  ω ^ ι 2  ≤   characteristic-ordinal (cut P n) (semidecCut P σ n)
     [2] =  ωⁿ≤right-summand
             (≤-trans H' (cut-complement σ n))
             (≤∘<-in-< (characteristic-ordinal-up-to-bounded P σ n)
                       (≤∘<-in-< (≤-refl-≡ [1])
                                 (x·-mono-< (λ p → lim≰zero (≤-refl-≡ p))
                                            ((ι-mono-< N.<-suc)))))


 characteristic-ordinal-characterisation
  : (σ : (n : ℕ) → semi-dec (P n))
  → ((n : ℕ) → isProp (P n))
  → down-closed P
  → ((n : ℕ) → P n) ↔ ω · ω ≤ characteristic-ordinal P σ
 characteristic-ordinal-characterisation σ Pprop P↓ = ∀nPn→ω²≤limF , ω²≤limF→∀nPn
  where
   F : ℕ → Brw
   F = characteristic-sequence P σ
   F↑ : increasing F
   F↑ = characteristic-sequence-increasing P σ
   -------1: simpler case, use key lemma 1
   ∀nPn→ω²≤limF : ((n : ℕ) → P n) → (ω · ω) ≤ limit F
   ∀nPn→ω²≤limF ρ =
    weakly-bisimilar→lim≤lim (λ n → limit ι · ι n) F (λ k → ∣ k , β k ∣)
     where
      β : (k : ℕ) → ω · ι k ≤ F k
      β k = ≤-trans (<-in-≤ (characteristic-ordinal-up-to-above-ωn P σ P↓ k (ρ k)))
                    Gk≤Fk
       where
        G : ℕ → Brw
        G n =  (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
        Gk≤Fk :  G k ≤ F k
        Gk≤Fk = x+-mono {_} {zero} {ι k} ≤-zero
    -------2: harder case, we cut the sequence in n and prove Pn
   ω²≤limF→∀nPn : (ω · ω) ≤ limit F → (n : ℕ) → P n
   ω²≤limF→∀nPn ω^2≤limitF n = subst P (N.+-zero n) (∥-∥rec (Qprop 0)  ∃mQm→Q0  ∃mQm)
    where
       Q = cut P n
       Qprop = isPropCut P Pprop n
       ρ = semidecCut P σ n
       Q-down-closed : down-closed Q
       Q-down-closed m Qsm = P↓ (n N+ m) (subst (λ i → P i) (+-suc n m) Qsm)
       FQ : ℕ → Brw
       FQ = characteristic-sequence Q ρ
       FQ↑ : increasing FQ
       FQ↑ = characteristic-sequence-increasing Q ρ
       GQ : ℕ → Brw
       GQ n =  (Q characteristic-ordinal-up-to n) (semi-dec-restrict-to n ρ)
       ω^2≤limitFQ : ω · ω ≤ characteristic-ordinal Q ρ
       ω^2≤limitFQ = cut-preserves-characteristic-ordinal-≥ω² σ n ω^2≤limitF
       ∃mω≤FQm : ∃[ m ∈ ℕ ] ω + ω ≤ FQ m
       ∃mω≤FQm = subst (λ z → ∃[ m ∈ ℕ ] z ≤ FQ m) (sym ω+ω≡ω·2 ) [1]
        where
         [1] : ∃[ m ∈ ℕ ] ω · ι 2 ≤ FQ m
         [1] =  lim≤lim→weakly-bisimilar (λ n₁ → limit ι · ι n₁) FQ ω^2≤limitFQ 2

       ∃mω≤GQm : ∃[ m ∈ ℕ ] ω + ω ≤ GQ m
       ∃mω≤GQm = ∥-∥rec PropTrunc.isPropPropTrunc [1] ∃mω≤FQm
        where
         [1] : Σ[ m ∈ ℕ ] ω + ω ≤ FQ m → ∃[ m ∈ ℕ ] ω + ω ≤ GQ m
         [1] (m , hm) = ∣ m , cancel-finite-lim-≤ (ω + ω) (GQ m)
                              ω+ω-islim m hm ∣
       ∃mQm : ∃[ m ∈ ℕ ] Q m
       ∃mQm = lr (characteristic-ordinal-up-to-spec Q ρ) ∃mω≤GQm
       ∃mQm→Q0 :  Σ[ m ∈ ℕ ] Q m → Q 0
       ∃mQm→Q0 (m , Qm) = ∀m-Qm→Q0 m Qm
        where
         ∀m-Qm→Q0 : (m : ℕ) → Q m → Q 0
         ∀m-Qm→Q0 zero q = q
         ∀m-Qm→Q0 (suc m) q = ∀m-Qm→Q0 m (Q-down-closed m q)
