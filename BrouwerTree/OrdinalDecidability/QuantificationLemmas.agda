{-# OPTIONS --cubical --erasure  --guardedness --lossy-unification #-}
module BrouwerTree.OrdinalDecidability.QuantificationLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc; predℕ; max) renaming (_+_ to _N+_)
import Cubical.Data.Nat.Order as N
import Cubical.Data.Nat.Properties as N
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Fin.Base


open import Iff
open import Bool
open import PropTrunc
open import FinChoice

open import BrouwerTree.Everything

open import BrouwerTree.OrdinalDecidability.Basic
open import BrouwerTree.OrdinalDecidability.GeneralProperties
open import BrouwerTree.OrdinalDecidability.QuantificationConstruction

private
 variable
  ℓ ℓ' : Level

module _
       (P : ℕ → Type ℓ)
      where
 open CharacteristicOrdinal P
 open CharacteristicOrdinal-Construction₁
 open CharacteristicOrdinal-Construction₂

 semi-dec-limit-ordinal-above-ωn+1 : down-closed P
                                   → (n : ℕ)
                                   → (σ : P semi-dec-str-up-to n)
                                   → ((i : ℕ) → i N.≤ n → P i)
                                   → ω · ι (suc n) ≤ semi-dec-limit-ordinal n σ
 semi-dec-limit-ordinal-above-ωn+1 P↓ zero σ _ =
  ≤-refl-≡ (limit-pointwise-equal
             (λ n → ω · ι 0 + ι n) ι
             (λ n → zero+y≡y (ι n)) ∙ sym (semi-dec-limit-ordinal-zero σ))
 semi-dec-limit-ordinal-above-ωn+1 P↓ (suc n) σ p =
  weakly-bisimilar→lim≤lim _ _ ([3'] [2] [1])
   where
    ρ =  semi-dec-str-restricted N.<-suc σ
    IH : ω · ι (suc n) ≤  semi-dec-limit-ordinal n ρ
    IH = semi-dec-limit-ordinal-above-ωn+1 P↓ n ρ
                                           (λ i i≤n → p i (N.≤-trans i≤n N.≤-sucℕ))
    [1] : ∃[ m ∈ ℕ ] ω · ι n ≤ ω-sequence n ρ m
    [1] = lim≤lim→weakly-bisimilar _ _ IH zero
    sseq-n = fst (σ n N.<-suc)
    tseq-n = Normalised-with-one (sseq-n)
    [2] :  ∃[ n ∈ ℕ ] tseq-n n ≡ true
    [2] = fst (Normalised-is-correct sseq-n) (fst (snd (σ n N.<-suc)) (p n N.≤-sucℕ))
    [3] : Σ[ n ∈ ℕ ] (tseq-n n ≡ true)
        → Σ[ m ∈  ℕ ] (ω · ι n ≤  ω-sequence n ρ m)
        → (λ k → ω · ι (suc n) + ι k) ≲ ω-sequence (suc n) σ
    [3] (z , hz) (v , hv) k  = ∣ v N+ z N+ k , ≤-trans [8] [9] ∣
     where
      [4] : suc (normal-seq-sum n ρ v)  N.≤ normal-seq-sum (suc n) σ (v N+ z)
      [4] = subst (suc (normal-seq-sum n ρ v)  N.≤_)
                  (sym (normal-seq-sum-suc {n = n} σ (v N+ z)))
                  [4-4]
       where
        s = normal-seq-sum n ρ (v N+ z) N+ Bool→Nat
                           (normal-seq (suc n) σ n N.<-suc (v N+ z))

        [4-1] : Bool→Nat (normal-seq (suc n) σ n N.<-suc (v N+ z)) ≡ 1
        [4-1] = cong Bool→Nat (Boolx≤y∧x≡t→y=t (Normalised-incr-+ z v) hz)
        [4-2] : suc (normal-seq-sum n ρ v) N.≤ suc (normal-seq-sum n  ρ (v N+ z))
        [4-2] = N.suc-≤-suc (normal-seq-sum-monotone n ρ v (v N+ z) N.≤SumLeft)
        [4-3] : s ≡ suc (normal-seq-sum n ρ (v N+ z))
        [4-3] =
         s
           ≡⟨ N.+-comm _ _ ⟩
         Bool→Nat (normal-seq (suc n) σ n N.<-suc (v N+ z)) N+ normal-seq-sum n ρ (v N+ z)
           ≡⟨ cong (_N+ normal-seq-sum n ρ (v N+ z)) [4-1] ⟩
         suc (normal-seq-sum n ρ (v N+ z))
           ∎
        [4-4] : suc (normal-seq-sum n ρ v) N.≤ s
        [4-4] = N.≤-trans [4-2] (subst (suc (normal-seq-sum n ρ (v N+ z)) N.≤_)
                                       (sym [4-3])
                                       N.≤-refl)
      [5] : ω · ι (suc (normal-seq-sum n ρ v)) ≤ ω · ι (normal-seq-sum (suc n) σ (v N+ z))
      [5] = x·-mono (ι-mono [4])
      [6] : ω · ι n ≤  ω · ι (normal-seq-sum n ρ v)
      [6] = ω·n≤ω·m+k→ω·n≤ω·m n (normal-seq-sum n ρ v) v hv
      [7] : ω · ι (suc n) ≤  ω · ι (normal-seq-sum  (suc n) σ (v N+ z))
      [7] = ≤-trans (+-mono {_}{ω}{_}{ω} [6] ≤-refl) [5]
      [8] :  ω · ι (suc n) + ι k ≤  ω · ι (normal-seq-sum (suc n) σ (v N+ z)) + ι ( v N+ z N+ k)
      [8] = +-mono {_} {ι k} {_} {ι (v N+ z N+ k)} [7] (ι-mono N.≤SumRight)
      [9] : ω · ι (normal-seq-sum (suc n) σ (v N+ z)) + ι ( v N+ z N+ k)
              ≤
            ω · ι (normal-seq-sum (suc n) σ (v N+ z N+ k)) + ι ( v N+ z N+ k)
      [9] = +-mono
             (x·-mono (ι-mono
                       (normal-seq-sum-monotone (suc n) σ (v N+ z)
                                                          (v N+ z N+ k)
                                                          N.≤SumLeft)))
             ≤-refl
    [3'] : ∃[ n ∈ ℕ ] tseq-n n ≡ true
         → ∃[ m ∈ ℕ ] ω · ι n ≤ ω-sequence n ρ m
         → (λ k → ω · ι (suc n) + ι k) ≲ ω-sequence (suc n) σ
    [3'] = ∥-∥rec (isPropΠ2 (λ _ _ → isPropPropTrunc))
                  (λ s → ∥-∥rec (isPropΠ (λ k → isPropPropTrunc)) ([3] s))

 characteristic-ordinal-up-to-above-ωn : (σ : (n : ℕ) → semi-dec (P n))
           → down-closed P
           → (n : ℕ)
           → P n
           → ω · ι n < (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
 characteristic-ordinal-up-to-above-ωn σ P↓ n p =
  characteristic-ordinal-up-to-reduction-lemma P σ (ω · ι n <_) (λ x → isProp⟨<⟩) [1]
   where
    [1] : (ρ : P semi-dec-str-up-to n) → ω · ι n < semi-dec-limit-ordinal n ρ
    [1] ρ = <∘≤-in-< (ω·n<ω·n+1 n) (semi-dec-limit-ordinal-above-ωn+1 P↓ n ρ ([2] n p))
      where
       [2] : (n : ℕ) → P n → (i : ℕ) → i N.≤ n → P i
       [2] n p' i (zero , hk) = subst (λ i → P i) (sym hk) p'
       [2] zero p' i i≤n@(suc k , hk) = subst (λ i → P i) (sym (N.≤0→≡0 i≤n)) p'
       [2] (suc n) p' i (suc k , hk) = [2] n (P↓ n p') i (k , cong predℕ hk)

 characteristic-ordinal-up-to-above-ω·2
  : (σ : (n : ℕ) → semi-dec (P n))
  → (n : ℕ)
  → P n
  → ω + ω ≤ (P characteristic-ordinal-up-to (suc n)) (semi-dec-restrict-to (suc n) σ)
 characteristic-ordinal-up-to-above-ω·2 σ  n p =
  characteristic-ordinal-up-to-reduction-lemma P σ (ω + ω ≤_) (λ x → isProp⟨≤⟩) [0]
   where
    [0] : (ρ : P semi-dec-str-up-to suc n) → ω + ω ≤ semi-dec-limit-ordinal (suc n) ρ
    [0] ρ = ω+ω≤semi-dec-limit-ordinal←Pn n ρ p

 characteristic-ordinal-up-to-spec
  : (σ : (n : ℕ) → semi-dec (P n))
  → ∃[ n ∈ ℕ ] ω + ω ≤ (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
  ↔ ∃[ n ∈ ℕ ] P n
 characteristic-ordinal-up-to-spec σ =
  ∥-∥rec isPropPropTrunc ξ , ∥-∥rec isPropPropTrunc τ
   where
    ξ : Σ[ n ∈ ℕ ] ω + ω ≤ (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
      → ∃[ n ∈ ℕ ] P n
    ξ (n , γ) = characteristic-ordinal-up-to-reduction-lemma P σ Q isProp⟨Q⟩ [0] γ
     where
      Q : Brw → Type ℓ
      Q x = ω + ω ≤ x → ∃[ n ∈ ℕ ] P n
      isProp⟨Q⟩ = λ x → isProp→ isPropPropTrunc

      [0] : {n : ℕ} → (ρ : P semi-dec-str-up-to n) → Q (semi-dec-limit-ordinal n ρ)
      [0] {n} ρ ω·2≤Ψ = ∥-∥rec isPropPropTrunc (λ (m , γ) → 0<normal-seq-sum→∃P n m ρ γ) ∃mtm>0
       where
        ψ = semi-dec-limit-ordinal n ρ
        ∃mω<gm : ∃[ m ∈ ℕ ] ω < ω-sequence n ρ m
        ∃mω<gm = ∥-∥rec PropTrunc.isPropPropTrunc [1] [2]
         where
          [1] : Σ[ m ∈  ℕ ] ω ≤ ω-sequence n ρ m → ∃[ m ∈ ℕ ] ω < ω-sequence n ρ m
          [1] (m , hm) = ∣ suc m , ≤-trans (≤-succ-mono hm) (ω-sequence-increasing n ρ m) ∣
          [2] : ∃[ m ∈ ℕ ] ω + ι zero  ≤ ω-sequence n ρ m
          [2] = lim≤lim→weakly-bisimilar  _ _  ω·2≤Ψ zero
        ∃mtm>0 :  ∃[ m ∈ ℕ ] 0 N.< normal-seq-sum n ρ m
        ∃mtm>0 = ∥-∥map η ∃mω<gm
         where
          η : Σ[ m ∈ ℕ ] ω < ω-sequence n ρ m → Σ[ m ∈ ℕ ] zero N.< normal-seq-sum n ρ m
          η (z , p) = z , ω·n>ω→n>0 (normal-seq-sum n ρ z) z p
    τ : Σ ℕ P
      → ∃[ n ∈ ℕ ] ω + ω ≤ (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
    τ (n , p) = ∣ suc n , characteristic-ordinal-up-to-above-ω·2 σ n p ∣

 characteristic-ordinal-up-to-spec'
  : (σ : (n : ℕ) → semi-dec (P n))
  → ∃[ n ∈ ℕ ] ω · ι 2 ≤ (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
  ↔ ∃[ n ∈ ℕ ] P n
 characteristic-ordinal-up-to-spec' σ =
  subst M ω+ω≡ω·2 (characteristic-ordinal-up-to-spec σ)
   where
    α : ℕ → Brw
    α n = (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n σ)
    M : Brw → Type ℓ
    M z = ∃[ n ∈ ℕ ] z ≤ (α n) ↔ ∃[ n ∈ ℕ ] P n

module _
        (P : ℕ → Type ℓ) (Q : ℕ → Type ℓ')
        (P-implies-Q : (n : ℕ) → P n → Q n)
       where
 open CharacteristicOrdinal
 open CharacteristicOrdinal-Construction₁
 open CharacteristicOrdinal-Construction₂


 normal-seq-sum-weakly-bisimilar
  : (n : ℕ)
  → (σ : P semi-dec-str-up-to n)
  → (τ : Q semi-dec-str-up-to n)
  → (k : ℕ)
  → ∃[ k' ∈ ℕ ] normal-seq-sum P n σ k N.≤ normal-seq-sum Q n τ k'
 normal-seq-sum-weakly-bisimilar zero σ τ k = ∣ (0 , (0 , refl)) ∣
 normal-seq-sum-weakly-bisimilar (suc n) σ τ k = ∥-∥rec squash [3] IH
  where
   𝕡 : {i : ℕ} → i N.< n → i N.< suc n
   𝕡 {i} l = snd (injectSuc (i , l))
   𝕢 : n N.< suc n
   𝕢 = snd flast

   ε : Bool → ℕ
   ε = Bool→Nat

   eval-σ : (j : ℕ) → Bool
   eval-σ j = Normalised-with-one (fst (σ n 𝕢)) j
   eval-τ : (j : ℕ) → Bool
   eval-τ j = Normalised-with-one (fst (τ n 𝕢)) j

   σ' : (i : ℕ) → i N.< n → semi-dec-str (P i)
   σ' i l = σ i (𝕡 l)

   τ' : (i : ℕ) → i N.< n → semi-dec-str (Q i)
   τ' i l = τ i (𝕡 l)

   [1] : normal-seq-sum P (suc n) σ k ≡ ε (eval-σ k) N+ normal-seq-sum P n σ' k
   [1] = refl

   [2] : normal-seq-sum Q (suc n) τ k ≡ ε (eval-τ k) N+ normal-seq-sum Q n τ' k
   [2] = refl

   IH : ∃[ k' ∈ ℕ ] normal-seq-sum P n σ' k N.≤ normal-seq-sum Q n τ' k'
   IH = normal-seq-sum-weakly-bisimilar n σ' τ' k

   [3] : Σ[ k' ∈ ℕ ] normal-seq-sum P n σ' k N.≤ normal-seq-sum Q n τ' k'
       → ∃[ k' ∈ ℕ ] normal-seq-sum P (suc n) σ k N.≤ normal-seq-sum Q (suc n) τ k'
   [3] (k' , l) = [4] (dichotomyBool (eval-σ k))
    where
     σₙ : ℕ → Bool
     σₙ = fst (σ n 𝕢)
     σₙ-spec : P n ↔ ∃[ j ∈ ℕ ] σₙ j ≡ true
     σₙ-spec = snd (σ n 𝕢)

     τₙ : ℕ → Bool
     τₙ = fst (τ n 𝕢)
     τₙ-spec : Q n ↔ ∃[ j ∈ ℕ ] τₙ j ≡ true
     τₙ-spec = snd (τ n 𝕢)

     ugoal = Σ ℕ (λ k' → normal-seq-sum P (suc n) σ k N.≤ normal-seq-sum Q (suc n) τ k')
     goal = ∥ ugoal ∥

     case-i : eval-σ k ≡ false → goal
     case-i e = ∣ (k' , N.≤-trans l₁ l₂) ∣
      where
       l₁ : ε (eval-σ k) N+ normal-seq-sum P n σ' k N.≤ normal-seq-sum Q n τ' k'
       l₁ = subst (λ - → - N.≤ normal-seq-sum Q n τ' k')
                  (sym (cong (λ - → ε - N+ normal-seq-sum P n σ' k) e))
                  l
       l₂ : normal-seq-sum Q n τ' k' N.≤ ε (eval-τ k') N+ normal-seq-sum Q n τ' k'
       l₂ = N.≤SumRight
     case-ii : eval-σ k ≡ true → goal
     case-ii e = ∥-∥map H eval-τ-is-true
      where
       pₙ : P n
       pₙ =
        rl σₙ-spec
           ∣ (rl (Normalised-is-correct-str σₙ) (k , e)) ∣
       qₙ : Q n
       qₙ = P-implies-Q n pₙ
       τₙ-holds : ∃[ m ∈ ℕ ] τₙ m ≡ true
       τₙ-holds = lr τₙ-spec qₙ
       eval-τ-is-true : ∃[ m ∈ ℕ ] eval-τ m ≡ true
       eval-τ-is-true = ∥-∥map (lr (Normalised-is-correct-str τₙ)) τₙ-holds

       H : Σ ℕ (λ m → eval-τ m ≡ true) → ugoal
       H (m , e') = N , N.≤-trans l₁ l₂
        where
         N = max k' m
         l₁ :     ε (eval-σ k) N+ normal-seq-sum P n σ' k
              N.≤ ε (eval-σ k) N+ normal-seq-sum Q n τ' N
         l₁ = N.≤-k+ (N.≤-trans l (normal-seq-sum-monotone Q n τ' k' N N.left-≤-max))
         l₂ :     ε (eval-σ k) N+ normal-seq-sum Q n τ' N
              N.≤ ε (eval-τ N) N+ normal-seq-sum Q n τ' N
         l₂ = N.≤-+k l₃
          where
           e'' : ε true ≡ ε (eval-τ N)
           e'' = cong ε h
            where
             h : true ≡ eval-τ N
             h = Bool-true≤→≡
                  (subst
                   (_B≤ eval-τ N)
                   e'
                   (Normalised-incr m N (N.right-≤-max {m} {k'})))
           l₃ : ε (eval-σ k) N.≤ ε (eval-τ N)
           l₃ = subst2 N._≤_ (cong ε (sym e)) e'' N.≤-refl

     [4] : (eval-σ k ≡ true) ⊎ (eval-σ k ≡ false)
         → ∃[ k'' ∈ ℕ ] normal-seq-sum P (suc n) σ k N.≤ normal-seq-sum Q (suc n) τ k''
     [4] = ⊎.rec case-ii case-i

 ω-sequence-weakly-bisimilar
  : (n : ℕ)
  → (σ : P semi-dec-str-up-to n)
  → (τ : Q semi-dec-str-up-to n)
  → ω-sequence P n σ ≲ ω-sequence Q n τ
 ω-sequence-weakly-bisimilar n σ τ k = ∥-∥map [1] (normal-seq-sum-weakly-bisimilar n σ τ k)
  where
   [1] : Σ ℕ (λ k' → normal-seq-sum P n σ k N.≤ normal-seq-sum Q n τ k')
       → Σ ℕ (λ k' → ω-sequence P n σ k ≤ ω-sequence Q n τ k')
   [1] (k' , l) =
    N ,
    (ω · ι (normal-seq-sum P n σ k) + ι k ≤⟨ l₁ ⟩
     ω · ι (normal-seq-sum P n σ k) + ι N ≤⟨ l₂ ⟩
     ω · ι (normal-seq-sum Q n τ k') + ι N    ≤⟨ l₃ ⟩
     ω · ι (normal-seq-sum Q n τ N) + ι N ≤∎)
      where
       N = max k' k
       l₁ = x+-mono {ω · ι (normal-seq-sum P n σ k)} (ι-mono (N.right-≤-max {k} {k'}))
       l₂ = +x-mono (ι N) (x·-mono (ι-mono l))
       l₃ = +x-mono (ι N)
             (x·-mono (ι-mono (normal-seq-sum-monotone Q n τ k' N N.left-≤-max)))


 semi-dec-limit-ordinal-mono
  : (n : ℕ)
  → (σ : P semi-dec-str-up-to n)
  → (τ : Q semi-dec-str-up-to n)
  → semi-dec-limit-ordinal P n σ ≤ semi-dec-limit-ordinal Q n τ
 semi-dec-limit-ordinal-mono n σ τ =
  weakly-bisimilar→lim≤lim
   (ω-sequence P n σ)
   (ω-sequence Q n τ)
   (ω-sequence-weakly-bisimilar n σ τ)


 characteristic-ordinal-up-to-mono
  : (n : ℕ)
  → (σ : (i : ℕ) → i N.< n → semi-dec (P i))
  → (τ : (i : ℕ) → i N.< n → semi-dec (Q i))
  → (P characteristic-ordinal-up-to n) σ ≤ (Q characteristic-ordinal-up-to n) τ
 characteristic-ordinal-up-to-mono n σ τ = ∥-∥rec ≤-trunc [1] (Finite-Choice n σ)
  where
   [1] : ((i : ℕ) → i N.< n → semi-dec-str (P i))
       → (P characteristic-ordinal-up-to n) σ ≤ (Q characteristic-ordinal-up-to n) τ
   [1] σ-data = ∥-∥rec ≤-trunc [2] (Finite-Choice n τ)
    where
     [2] : ((i : ℕ) → i N.< n → semi-dec-str (Q i))
         → (P characteristic-ordinal-up-to n) σ ≤ (Q characteristic-ordinal-up-to n) τ
     [2] τ-data =
      subst2 _≤_
       (characteristic-ordinal-up-to-compatible P n σ σ-data)
       (characteristic-ordinal-up-to-compatible Q n τ τ-data)
       (semi-dec-limit-ordinal-mono n σ-data τ-data)

 characteristic-sequence-mono
  : (σ : (n : ℕ) → semi-dec (P n))
  → (τ : (n : ℕ) → semi-dec (Q n))
  → (n : ℕ) → characteristic-sequence P σ n ≤ characteristic-sequence Q τ n
 characteristic-sequence-mono σ τ n =
  +x-mono (ι n) (characteristic-ordinal-up-to-mono n (semi-dec-restrict-to n σ)
                                                     (semi-dec-restrict-to n τ))

 characteristic-ordinal-mono
  : (σ : (n : ℕ) → semi-dec (P n))
  → (τ : (n : ℕ) → semi-dec (Q n))
  → characteristic-ordinal P σ ≤ characteristic-ordinal Q τ
 characteristic-ordinal-mono σ τ = pointwise≤→≤ (characteristic-sequence-mono σ τ)
