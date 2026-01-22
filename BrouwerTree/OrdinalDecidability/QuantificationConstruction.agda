{-# OPTIONS --cubical --erasure --guardedness #-}
module BrouwerTree.OrdinalDecidability.QuantificationConstruction where

open import Cubical.Data.Nat
  using (ℕ; zero; suc; ·-comm ; max ; +-zero ; +-suc ; isSetℕ)
  renaming (_+_ to _N+_; _·_ to _N·_; +-assoc to N+-assoc)
import Cubical.Data.Nat.Order as N
import Cubical.Data.Nat.Properties as N
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum as S
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Fin.Base

open import Iff
open import Bool
open import FinChoice
open import PropTrunc

open import BrouwerTree.Everything

open import BrouwerTree.OrdinalDecidability.Basic
open import BrouwerTree.OrdinalDecidability.GeneralProperties

private
 variable
  ℓ ℓ' : Level

-----------------------------------------------------------------------------------
--------------------------------PART I : Preliminaries:---------------------------

------------------------

-- Normalising a boolean sequence:
Normalised-with-one : (s : ℕ → Bool) → (ℕ → Bool)
Normalised-with-one s zero = s zero
Normalised-with-one s (suc k) = (Normalised-with-one s k) or (s (suc k))

------
sn≤normalsn : {s : ℕ → Bool} → {n : ℕ} → s n B≤ Normalised-with-one s n
sn≤normalsn {n = zero} = Bool-≤-refl
sn≤normalsn {n = suc n} = Bool-≤-or-2 Bool-≤-refl

Normalised-incr-+ : {s : ℕ → Bool} → (u k : ℕ) → Normalised-with-one s u B≤ Normalised-with-one s (k N+ u)
Normalised-incr-+ u zero = Bool-≤-refl
Normalised-incr-+ u (suc k) = Bool-≤-or (Normalised-incr-+ u k)


Normalised-incr : {s : ℕ → Bool} → (m n : ℕ)  →  (m N.≤ n) → Normalised-with-one s m B≤ Normalised-with-one s n
Normalised-incr {s} m n p = subst (λ z →  Normalised-with-one s m B≤ Normalised-with-one s z )
                                   (p .snd) (Normalised-incr-+ m (p .fst))

------
or-⊎ : {x y : Bool} → (x or y ≡ true) → (x ≡ true) ⊎ (y ≡ true)
or-⊎ {false} {y} p = inr p
or-⊎ {true} {y} p = inl p

-----

Normalised-is-correct : (s : ℕ → Bool)
                      → ∃[ k ∈ ℕ ] s k ≡ true
                      ↔ ∃[ k ∈ ℕ ] Normalised-with-one s k ≡ true
Normalised-is-correct s =  (∥-∥map [1]) , (∥-∥rec (PropTrunc.isPropPropTrunc)
                                           λ z → [2] (z .fst) (z. snd))
  where
    [1] : Σ[ k ∈ ℕ ] s k ≡ true → Σ[ k ∈ ℕ ] Normalised-with-one s k ≡ true
    [1] (zero , hm) = zero , hm
    [1] (suc m , hm) = (suc m) , Bool-or-introR hm

    [2] : (k : ℕ) → Normalised-with-one s k ≡ true → ∃[ k ∈ ℕ ] s k ≡ true
    [2] zero  h0 = ∣ zero , h0 ∣
    [2] (suc m)  hsm = [3] (or-⊎ hsm)
     where
      [3] : (Normalised-with-one s m ≡ true) ⊎ (s (suc m) ≡ true) → ∃[ k ∈ ℕ ] s k ≡ true
      [3] = S.rec (λ hm → [2] m hm) (λ p → ∣ (suc m) , p ∣)

Normalised-is-correct' : (s : ℕ → Bool)
                      → (k : ℕ)
                      → (Σ[ k' ∈ ℕ ] ((k' N.≤ k) × (s k' ≡ true))) ↔ (Normalised-with-one s k ≡ true)
Normalised-is-correct' s k = [1] , [2] k
  where
    [1] : Σ[ k' ∈ ℕ ] ((k' N.≤ k) × (s k' ≡ true)) → (Normalised-with-one s k ≡ true)
    [1] (0 , p , t) = Boolx≤y∧x≡t→y=t (Normalised-incr {s} 0 k p) t
    [1] (suc k' , p , t) = Boolx≤y∧x≡t→y=t (Normalised-incr {s} (suc k') k p) (Bool-or-introR t)

    [2] : (k : ℕ) → Normalised-with-one s k ≡ true → Σ[ k' ∈ ℕ ] ((k' N.≤ k) × (s k' ≡ true))
    [2] zero t = 0 , N.≤-refl , t
    [2] (suc k) t with or-⊎ {Normalised-with-one s k} {s (suc k)} t
    ... | inl x = let (k' , p , e) = [2] k x in k' , N.≤-suc p , e
    ... | inr x = suc k , N.≤-refl , x

Normalised-is-correct-str : (s : ℕ → Bool)
                          → Σ ℕ ( λ k → (s k ≡ true))
                          ↔ Σ ℕ ( λ k → (Normalised-with-one s k ≡ true))
Normalised-is-correct-str s = [1] , [2]
 where
  [1] : Σ ℕ ( λ k → (s k ≡ true)) → Σ ℕ ( λ k → (Normalised-with-one s k ≡ true))
  [1] (k , t) = k , lr (Normalised-is-correct' s k) (k , N.≤-refl , t)
  [2] : Σ ℕ ( λ k → (Normalised-with-one s k ≡ true)) → Σ ℕ ( λ k → (s k ≡ true))
  [2] (k , t) = let (k' , p , t') = rl (Normalised-is-correct' s k) t in k' , t'

----------------------------------------------------------------------

_semi-dec-str-up-to_ : (ℕ → Type ℓ) → ℕ → Type ℓ
P semi-dec-str-up-to n = (i : ℕ) → i N.< n → semi-dec-str (P i)

_semi-dec-up-to_ : (ℕ → Type ℓ) → ℕ → Type ℓ
P semi-dec-up-to n = (i : ℕ) → i N.< n → semi-dec (P i)

semi-dec-restrict-to : {P : ℕ → Type ℓ} (n : ℕ)
                     → ((i : ℕ) → semi-dec (P i))
                     → P semi-dec-up-to n
semi-dec-restrict-to n σ i _ = σ i

module CharacteristicOrdinal
        (P : ℕ → Type ℓ)
       where

 semi-dec-str-restricted : {k n : ℕ}
                         → k N.< n
                         → P semi-dec-str-up-to n
                         → P semi-dec-str-up-to k
 semi-dec-str-restricted k<n σ i i<k = σ i (N.<-trans i<k k<n)

 semi-dec-str-restricted-≤ : {k n : ℕ}
                           → k N.≤ n
                           → P semi-dec-str-up-to n
                           → P semi-dec-str-up-to k
 semi-dec-str-restricted-≤ k≤n σ i i<k = σ i (N.<≤-trans i<k k≤n)

 module CharacteristicOrdinal-Construction₁
        (n : ℕ)
        (σ : P semi-dec-str-up-to n)
       where

  normal-seq : (i : ℕ) → i N.< n → (ℕ → Bool)
  normal-seq i i<n = Normalised-with-one (fst (σ i i<n))

  normal-seq-sum : ℕ → ℕ
  normal-seq-sum k = sumFinGen _N+_ 0 (λ (i , l) → Bool→Nat (normal-seq i l k))

 module _ where
  open CharacteristicOrdinal-Construction₁

  normal-seq-sim : (n : ℕ) (σ₁ σ₂ : P semi-dec-str-up-to n)
                   (i : ℕ) (l : i N.< n) (k : ℕ)
                 → ∃[ m ∈ ℕ ] normal-seq n σ₁ i l k B≤ normal-seq n σ₂ i l m
  normal-seq-sim n σ₁ σ₂ i l k with (normal-seq n σ₁ i l k) UsingEq
  ... | true , e = ∥-∥map (map-snd λ e' → Bool≡→≤ (e ∙ sym e')) [2]
   where
     s₁ : ℕ → Bool
     s₁ = fst (σ₁ i l)
     s₁-spec : P i ↔ ∃[ n ∈ ℕ ] s₁ n ≡ true
     s₁-spec = snd (σ₁ i l)
     s₂ : ℕ → Bool
     s₂ = fst (σ₂ i l)
     s₂-spec : P i ↔ ∃[ n ∈ ℕ ] s₂ n ≡ true
     s₂-spec = snd (σ₂ i l)
     [1] : Σ[ m ∈ ℕ ] s₁ m ≡ true
     [1] = rl (Normalised-is-correct-str s₁) (k , e)
     [2] : ∃[ m ∈ ℕ ] normal-seq n σ₂ i l m ≡ true
     [2] = lr (Normalised-is-correct s₂) (lr s₂-spec (rl s₁-spec ∣ [1] ∣))
  ... | false , e = ∣ k , subst (_B≤ normal-seq n σ₂ i l k) (sym e) tt ∣

  normal-seq-sum-zero : (σ : P semi-dec-str-up-to 0) (k : ℕ)
                      → normal-seq-sum 0 σ k ≡ 0
  normal-seq-sum-zero σ k = refl

  normal-seq-sum-one : (σ : P semi-dec-str-up-to 1) (k : ℕ)
                     → normal-seq-sum 1 σ k ≡ Bool→Nat (normal-seq 1 σ 0 N.<-suc k)
  normal-seq-sum-one σ k = +-zero (Bool→Nat (normal-seq 1 σ 0 N.<-suc k))

  normal-seq-sum-suc : {n : ℕ} (σ : P semi-dec-str-up-to (suc n)) (k : ℕ)
                     → normal-seq-sum (suc n) σ k
                       ≡ normal-seq-sum n (semi-dec-str-restricted N.<-suc σ) k
                         N+ Bool→Nat (normal-seq (suc n) σ n N.<-suc k)
  normal-seq-sum-suc {n} σ k = N.+-comm N₃ N₁ ∙ cong (N₁ N+_) e
   where
    N₁ = normal-seq-sum n (semi-dec-str-restricted N.<-suc σ) k
    N₂ = Bool→Nat (normal-seq (suc n) σ n N.<-suc k)
    N₃ = Bool→Nat (normal-seq (suc n) σ n (snd flast) k)
    e : N₃ ≡ N₂
    e = cong (λ - → Bool→Nat (normal-seq (suc n) σ n - k)) (N.isProp≤ (snd flast) N.<-suc)

  normal-seq-sum-increasing
   : (n : ℕ) (σ : P semi-dec-str-up-to (suc n)) (k : ℕ)
   → normal-seq-sum n (semi-dec-str-restricted N.<-suc σ) k
     N.≤ normal-seq-sum (suc n) σ k
  normal-seq-sum-increasing n σ k = M , e
   where
    N₁ = normal-seq-sum n (semi-dec-str-restricted N.<-suc σ) k
    N₂ = normal-seq-sum (suc n) σ k
    M = Bool→Nat (normal-seq (suc n) σ n N.<-suc k)
    e : M N+ N₁ ≡ N₂
    e = N.+-comm M N₁ ∙ sym (normal-seq-sum-suc σ k)

  normal-seq-sum-monotone : (n : ℕ) (σ : P semi-dec-str-up-to n) (k₁ k₂ : ℕ)
                          → k₁ N.≤ k₂
                          → normal-seq-sum n σ k₁ N.≤ normal-seq-sum n σ k₂
  normal-seq-sum-monotone zero σ k₁ k₂ l =
   subst2 N._≤_ (sym (normal-seq-sum-zero σ k₁))
                (sym (normal-seq-sum-zero σ k₂))
                N.≤-refl
  normal-seq-sum-monotone (suc n) σ k₁ k₂ l =
   subst2 N._≤_ (sym (normal-seq-sum-suc σ k₁))
                (sym (normal-seq-sum-suc σ k₂))
                (N.≤-+-≤ (normal-seq-sum-monotone n
                           (semi-dec-str-restricted N.<-suc σ) k₁ k₂ l)
                         (Bool→Nat-mono (Normalised-incr k₁ k₂ l)))

  normal-seq-sum-bounded
   : (n : ℕ) (σ : P semi-dec-str-up-to (suc n)) (k : ℕ)
   → normal-seq-sum (suc n) σ k
     N.≤ normal-seq-sum n (semi-dec-str-restricted N.<-suc σ) k N+ 1
  normal-seq-sum-bounded n σ k =
   subst (N._≤ normal-seq-sum n (semi-dec-str-restricted N.<-suc σ) k N+ 1)
         (sym (normal-seq-sum-suc σ k))
         (N.≤-k+ (Bool→Nat-mono (Bool≤true {normal-seq (suc n) σ n N.<-suc k})))

  normal-seq-sum-sim
   : (n : ℕ) (σ₁ σ₂ : P semi-dec-str-up-to n) (k : ℕ)
   → ∃[ m ∈ ℕ ] normal-seq-sum n σ₁ k N.≤ normal-seq-sum n σ₂ m
  normal-seq-sum-sim zero σ₁ σ₂ k =
   ∣ zero ,
     subst (N._≤ normal-seq-sum zero σ₂ k)
           (sym (normal-seq-sum-zero σ₂ k))
           N.zero-≤ ∣
  normal-seq-sum-sim (suc n) σ₁ σ₂ k = ∥-∥rec squash h₁ lem
   where
    ψ = normal-seq-sum n
    ϕ = normal-seq (suc n)

    lem : ∃[ m ∈ ℕ ] ϕ σ₁ n N.<-suc k B≤ ϕ σ₂ n N.<-suc m
    lem = normal-seq-sim (suc n) σ₁ σ₂ n N.<-suc k

    h₁ : Σ[ m ∈ ℕ ] ϕ σ₁ n N.<-suc k B≤ ϕ σ₂ n N.<-suc m
       → ∃[ m ∈ ℕ ] normal-seq-sum (suc n) σ₁ k N.≤ normal-seq-sum (suc n) σ₂ m
    h₁ (m₁ , [1]) = ∥-∥map h₂ (normal-seq-sum-sim n τ₁ τ₂ k)
     where
      τ₁ = semi-dec-str-restricted N.<-suc σ₁
      τ₂ = semi-dec-str-restricted N.<-suc σ₂

      h₂ : Σ ℕ (λ m → ψ τ₁ k N.≤ ψ τ₂ m)
              → Σ ℕ (λ m → normal-seq-sum (suc n) σ₁ k
                           N.≤ normal-seq-sum (suc n) σ₂ m)
      h₂ (m₂ , [2]) = m , [4]
       where
        m : ℕ
        m = N.max m₁ m₂

        [3] = ψ τ₁ k  N+ Bool→Nat (ϕ σ₁ n N.<-suc k)  ≤[ [3]₁ ]
              ψ τ₂ m₂ N+ Bool→Nat (ϕ σ₁ n N.<-suc k)  ≤[ [3]₂ ]
              ψ τ₂ m  N+ Bool→Nat (ϕ σ₁ n N.<-suc k)  ≤[ [3]₃ ]
              ψ τ₂ m  N+ Bool→Nat (ϕ σ₂ n N.<-suc m₁) ≤[ [3]₄ ]
              ψ τ₂ m  N+ Bool→Nat (ϕ σ₂ n N.<-suc m)  ≤[ N.≤-refl ]
              N.≤-refl
         where
          open N.<-Reasoning renaming (_≤⟨_⟩_ to _≤[_]_)
          [3]₁ = N.≤-+k [2]
          [3]₂ = N.≤-+k (normal-seq-sum-monotone n τ₂ m₂ m
                                                 (N.right-≤-max {m₂} {m₁}))
          [3]₃ = N.≤-k+ (Bool→Nat-mono [1])
          [3]₄ = N.≤-k+ {Bool→Nat (ϕ σ₂ n N.<-suc m₁)}
                        {Bool→Nat (ϕ σ₂ n N.<-suc m)}
                        {ψ τ₂ m}
                        (Bool→Nat-mono {ϕ σ₂ n N.<-suc m₁}
                                       {ϕ σ₂ n N.<-suc m}
                                       [3]₅)
           where
            [3]₅ : ϕ σ₂ n (N.<-suc {n}) m₁ B≤ ϕ σ₂ n (N.<-suc {n}) m
            [3]₅ = Normalised-incr {fst (σ₂ n N.<-suc)} m₁ m (N.left-≤-max)

        [4] : normal-seq-sum (suc n) σ₁ k N.≤ normal-seq-sum (suc n) σ₂ m
        [4] = subst2 N._≤_ (sym (normal-seq-sum-suc σ₁ k))
                           (sym (normal-seq-sum-suc σ₂ m))
                           [3]

  0<normal-seq-sum→∃P : (n m : ℕ) (σ : P semi-dec-str-up-to n)
                      → 0 N.< normal-seq-sum n σ m
                      → ∃ ℕ P
  0<normal-seq-sum→∃P zero m σ h =
   ⊥.rec (N.¬-<-zero (subst (zero N.<_) (normal-seq-sum-zero σ m) h))
  0<normal-seq-sum→∃P (suc n) m σ h with normal-seq (suc n) σ n N.<-suc m ≟ true
  ... | yes v = ∣ n , rl (snd s)
                         (rl (Normalised-is-correct (fst s)) ∣ (m , v) ∣) ∣
   where
    s : semi-dec-str (P n)
    s = σ n N.<-suc
  ... | no u = 0<normal-seq-sum→∃P n m τ h'
   where
    τ = semi-dec-str-restricted N.<-suc σ
    h' : 0 N.< normal-seq-sum n τ m
    h' = N.<≤-trans h (N.≤-reflexive (normal-seq-sum-suc σ m ∙ e₂))
     where
      e₁ : Bool→Nat (normal-seq (suc n) σ n N.<-suc m) ≡ 0
      e₁ = cong Bool→Nat (¬true→false ((normal-seq (suc n) σ n N.<-suc m)) u)
      e₂ : normal-seq-sum n τ m N+ Bool→Nat (normal-seq (suc n) σ n N.<-suc m)
           ≡ normal-seq-sum n τ m
      e₂ = cong (normal-seq-sum n τ m N+_) e₁ ∙ +-zero (normal-seq-sum n τ m)

  0<normal-seq-sum←Pn : (n : ℕ) (σ : P semi-dec-str-up-to (suc n))
                      → P n
                      → ∃[ m ∈ ℕ ] 0 N.< normal-seq-sum (suc n) σ m
  0<normal-seq-sum←Pn n σ p = ∥-∥map [3] [2]
   where
    s : ℕ → Bool
    s = fst (σ n N.<-suc)
    s-spec : P n ↔ ∃[ m ∈ ℕ ] s m ≡ true
    s-spec = snd (σ n N.<-suc)
    [1] : ∃[ m ∈ ℕ  ] s m ≡ true
    [1] = lr s-spec p
    [2] : ∃[ m ∈ ℕ ] normal-seq (suc n) σ n N.<-suc m ≡ true
    [2] = lr (Normalised-is-correct s) [1]
    [3] : Σ[ m ∈ ℕ ] normal-seq (suc n) σ n N.<-suc m ≡ true
        → Σ[ m ∈ ℕ ] 0 N.< normal-seq-sum (suc n) σ m
    [3] (m , e) =
     m , N.<≤-trans
          (N.<≤-trans (subst (0 N.<_) (cong Bool→Nat (sym e)) N.<-suc)
                      N.≤SumRight)
          (N.≤-reflexive (sym (normal-seq-sum-suc σ m)))

 module CharacteristicOrdinal-Construction₂
        (n : ℕ)
        (σ : P semi-dec-str-up-to n)
       where

  open CharacteristicOrdinal-Construction₁ n σ

  ω-sequence : ℕ → Brw
  ω-sequence = ω·-sequence normal-seq-sum

  ω-sequence-increasing : increasing ω-sequence
  ω-sequence-increasing =
   ω·-sequence-increasing normal-seq-sum
    (λ m → normal-seq-sum-monotone n σ m (suc m) (N.≤-suc N.≤-refl))

  semi-dec-limit-ordinal : Brw
  semi-dec-limit-ordinal = limit ω-sequence {ω-sequence-increasing}

 module _ where
  open CharacteristicOrdinal-Construction₂

  ω-sequence-n≤sn : (n k : ℕ) (σ : P semi-dec-str-up-to (suc n))
                  → ω-sequence n (semi-dec-str-restricted N.<-suc σ) k
                    ≤ ω-sequence (suc n) σ k
  ω-sequence-n≤sn n k σ = +-mono {_} {ι k} [1] ≤-refl
   where
    open CharacteristicOrdinal-Construction₁
    [1] : ω · ι (normal-seq-sum n (semi-dec-str-restricted N.<-suc σ) k)
          ≤ ω · ι (normal-seq-sum (suc n) σ k)
    [1] = x·-mono (ι-mono (normal-seq-sum-increasing n σ k))

  semi-dec-limit-ordinal-zero : (σ : P semi-dec-str-up-to 0)
                              → semi-dec-limit-ordinal 0 σ ≡ ω
  semi-dec-limit-ordinal-zero σ =
   limit-pointwise-equal (ω-sequence 0 σ) ι (λ k → zero+y≡y (ι k))

  semi-dec-limit-ordinal-weakly-constant :
   (n : ℕ) → Weakly-Constant (semi-dec-limit-ordinal n)
  semi-dec-limit-ordinal-weakly-constant n σ₁ σ₂ =
   bisim (ω-sequence n σ₁) (ω-sequence n σ₂) (lem σ₁ σ₂ , lem σ₂ σ₁)
    where
     lem : (σ τ : P semi-dec-str-up-to n) → ω-sequence n σ ≲ ω-sequence n τ
     lem σ τ k = ∥-∥map helper (normal-seq-sum-sim n σ τ k)
      where
       open CharacteristicOrdinal-Construction₁ n
       helper : (Σ ℕ (λ m → normal-seq-sum σ k N.≤ normal-seq-sum τ m))
              → Σ ℕ (λ m → ω-sequence n σ k ≤ ω-sequence n τ m)
       helper (m , l) = (m N+ k , +-mono {_} {ι k} {_} {ι (m N+ k)}
                                   (x·-mono (ι-mono l'))
                                   (ι-mono N.≤SumRight))
        where
         l' : normal-seq-sum σ k N.≤ normal-seq-sum τ (m N+ k)
         l' = N.≤-trans l (normal-seq-sum-monotone n τ m (m N+ k) N.≤SumLeft)

  semi-dec-limit-ordinal-increasing
   : (n : ℕ) (σ : P semi-dec-str-up-to n) (τ : P semi-dec-str-up-to (suc n))
   → semi-dec-limit-ordinal n σ ≤ semi-dec-limit-ordinal (suc n) τ
  semi-dec-limit-ordinal-increasing n σ τ =
   ≤-trans
    (≤-refl-≡ (semi-dec-limit-ordinal-weakly-constant n σ
                (semi-dec-str-restricted N.<-suc τ)))
    (pointwise≤→≤ (λ k → ω-sequence-n≤sn n k τ))

  semi-dec-limit-ordinal-increasing'
   : (n k : ℕ) (σ : P semi-dec-str-up-to (n N+ k))
   → semi-dec-limit-ordinal k (semi-dec-str-restricted-≤ N.≤SumRight σ)
     ≤ semi-dec-limit-ordinal (n N+ k) σ
  semi-dec-limit-ordinal-increasing' zero k σ =
   ≤-refl-≡ (semi-dec-limit-ordinal-weakly-constant k
              (semi-dec-str-restricted-≤ N.≤SumRight σ) σ)
  semi-dec-limit-ordinal-increasing' (suc n) k σ =
   semi-dec-limit-ordinal k τ₁             ≤⟨ l₁ ⟩
   semi-dec-limit-ordinal k τ₃             ≤⟨ l₂ ⟩
   semi-dec-limit-ordinal (n N+ k) τ₂      ≤⟨ l₃ ⟩
   semi-dec-limit-ordinal (suc (n N+ k)) σ ≤∎
    where
     τ₁ = semi-dec-str-restricted-≤ {k} {suc n N+ k} N.≤SumRight σ
     τ₂ = semi-dec-str-restricted-≤ {n N+ k} {suc (n N+ k)} (N.≤-suc N.≤-refl) σ
     τ₃ = semi-dec-str-restricted-≤ {k} {n N+ k} N.≤SumRight τ₂
     l₁ = ≤-refl-≡ (semi-dec-limit-ordinal-weakly-constant k τ₁ τ₃)
     l₂ = semi-dec-limit-ordinal-increasing' n k τ₂
     l₃ = semi-dec-limit-ordinal-increasing (n N+ k) τ₂ σ

  semi-dec-limit-ordinal-bounded : (n : ℕ) (σ : P semi-dec-str-up-to n)
                                   (τ : P semi-dec-str-up-to (suc n))
                                 → semi-dec-limit-ordinal (suc n) τ
                                   ≤ semi-dec-limit-ordinal n σ + ω
  semi-dec-limit-ordinal-bounded n σ τ =
   subst (λ - → semi-dec-limit-ordinal (suc n) τ ≤ - + ω)
         (semi-dec-limit-ordinal-weakly-constant n ρ σ)
         [1]
    where
     open CharacteristicOrdinal-Construction₁
     ρ = semi-dec-str-restricted N.<-suc τ
     [1] : semi-dec-limit-ordinal (suc n) τ ≤ semi-dec-limit-ordinal n ρ + ω
     [1] = limit-of-ω·-sequence-≤
            (normal-seq-sum n ρ)
            (normal-seq-sum (suc n) τ)
            (λ k → normal-seq-sum-monotone n ρ k (suc k) N.≤-sucℕ)
            (λ k → normal-seq-sum-monotone (suc n) τ k (suc k) N.≤-sucℕ)
            (normal-seq-sum-bounded n τ)

  ω+ω≤semi-dec-limit-ordinal←Pn : (n : ℕ) (σ : P semi-dec-str-up-to (suc n))
                                → P n → ω + ω ≤ semi-dec-limit-ordinal (suc n) σ
  ω+ω≤semi-dec-limit-ordinal←Pn n σ p =
   weakly-bisimilar→lim≤lim _ _ (λ k → [1] k (0<normal-seq-sum←Pn n σ p))
   where
    open CharacteristicOrdinal-Construction₁
    [1] : (k : ℕ)
        → ∃[ m ∈ ℕ ] 0 N.< normal-seq-sum (suc n) σ m
        → ∃[ m ∈ ℕ ] ω + ι k ≤ ω-sequence (suc n) σ m
    [1] k = ∥-∥map [2]
     where
      [2] : Σ[ m ∈ ℕ ] 0 N.< normal-seq-sum (suc n) σ m
          → Σ[ m ∈ ℕ ] ω + ι k ≤ ω-sequence (suc n) σ m
      [2] (m , l) = (m N+ k ,
                     +-mono {y = ι k} {y' = ι (m N+ k)} [3] (ι-mono N.≤SumRight))
       where
        [3] = ω
               ≤⟨ ≤-refl-≡ (sym ω·1≡ω) ⟩
              ω · ι 1
               ≤⟨ x·-mono
                   (ι-mono
                    (N.≤-trans l
                      (normal-seq-sum-monotone (suc n) σ m (m N+ k)
                                               N.≤SumLeft))) ⟩
              ω · ι (normal-seq-sum (suc n) σ (m N+ k)) ≤∎

  semi-dec-limit-ordinal-weakly-constant-factorisation
   : (n : ℕ)
   → Σ (∥ P semi-dec-str-up-to n ∥ → Brw)
       (λ Ψ → (σ : P semi-dec-str-up-to n)
            → semi-dec-limit-ordinal n σ ≡ Ψ ∣ σ ∣)
  semi-dec-limit-ordinal-weakly-constant-factorisation n =
   WC-Factorisation trunc (semi-dec-limit-ordinal n)
                          (semi-dec-limit-ordinal-weakly-constant n)

module _ where
 open CharacteristicOrdinal
 open CharacteristicOrdinal-Construction₂

 construction-of_characteristic-ordinal-up-to_
  : (P : ℕ → Type ℓ) (n : ℕ)
  → Σ (P semi-dec-up-to n → Brw)
      (λ Ψ → (σ : P semi-dec-str-up-to n)
           → semi-dec-limit-ordinal P n σ ≡ Ψ (λ i l → ∣ σ i l ∣))
 construction-of P characteristic-ordinal-up-to n = Ψ , [2]
  where
   [1] : Σ (∥ P semi-dec-str-up-to n ∥ → Brw)
           (λ Ψ' → (σ : P semi-dec-str-up-to n)
                 → semi-dec-limit-ordinal P n σ ≡ Ψ' ∣ σ ∣)
   [1] = semi-dec-limit-ordinal-weakly-constant-factorisation P n
   Ψ' : ∥ P semi-dec-str-up-to n ∥ → Brw
   Ψ' = fst [1]
   Ψ : P semi-dec-up-to n → Brw
   Ψ σ = Ψ' (Finite-Choice n σ)

   [2] : (σ : P semi-dec-str-up-to n)
       → semi-dec-limit-ordinal P n σ ≡ Ψ (λ i l → ∣ σ i l ∣)
   [2] σ =
    semi-dec-limit-ordinal P n σ ≡⟨ snd [1] σ ⟩
    Ψ' ∣ σ ∣                     ≡⟨ cong Ψ' (sym [3]) ⟩
    Ψ (λ i l → ∣ σ i l ∣)        ∎
     where
      [3] : Finite-Choice n (λ i l → ∣ σ i l ∣) ≡ ∣ σ ∣
      [3] = PropTrunc.isPropPropTrunc _ _

 _characteristic-ordinal-up-to_ : (P : ℕ → Type ℓ) (n : ℕ)
                                → P semi-dec-up-to n
                                → Brw
 P characteristic-ordinal-up-to n =
  fst (construction-of P characteristic-ordinal-up-to n)

module _
        (P : ℕ → Type ℓ) (n : ℕ)
       where
 open CharacteristicOrdinal
 open CharacteristicOrdinal-Construction₂

 characteristic-ordinal-up-to-weakly-constant :
  Weakly-Constant (P characteristic-ordinal-up-to n)
 characteristic-ordinal-up-to-weakly-constant σ τ =
  cong (P characteristic-ordinal-up-to n)
       (isPropΠ2 (λ _ _ → PropTrunc.isPropPropTrunc) σ τ)

 characteristic-ordinal-up-to-compatible
  : (s : P semi-dec-up-to n)
    (σ : P semi-dec-str-up-to n)
  → semi-dec-limit-ordinal P n σ ≡ (P characteristic-ordinal-up-to n) s
 characteristic-ordinal-up-to-compatible s σ =
  snd (construction-of P characteristic-ordinal-up-to n) σ
  ∙ characteristic-ordinal-up-to-weakly-constant
     (λ i l → ∣ σ i l ∣)
     s

{-
  In the following we assume that the family P is semi-decidable everywhere,
  although it would suffice to assume that P is semi-decidable up to some n,
  with n depending on the particular lemma involved.
-}

module _
        (P : ℕ → Type ℓ)
        (P-semi-dec : (n : ℕ) → semi-dec (P n))
       where

 private
  P-semi-dec↓ : {n : ℕ} → P semi-dec-up-to n
  P-semi-dec↓ {n} = semi-dec-restrict-to n P-semi-dec

 open CharacteristicOrdinal
 open CharacteristicOrdinal-Construction₂

 -- A general lemma for proving properties of the characteristic ordinal up to
 -- some n : ℕ.
 characteristic-ordinal-up-to-reduction-lemma
  : (F : Brw → Type ℓ')
  → ((x : Brw) → isProp (F x))
  → {n : ℕ}
  → ((σ : P semi-dec-str-up-to n) → F (semi-dec-limit-ordinal P n σ))
  → F ((P characteristic-ordinal-up-to n) P-semi-dec↓)
 characteristic-ordinal-up-to-reduction-lemma F F-is-prop {n} hyp =
  ∥-∥rec (F-is-prop ((P characteristic-ordinal-up-to n) P-semi-dec↓))
         (λ σ →
          subst F
                (characteristic-ordinal-up-to-compatible P n P-semi-dec↓ σ)
                (hyp σ))
         (Finite-Choice n P-semi-dec↓)

 characteristic-ordinal-up-to-reduction-lemma₂
  : (F : Brw → Brw → Type ℓ')
  → ((x y : Brw) → isProp (F x y))
  → {n m : ℕ}
  → ((σ : P semi-dec-str-up-to n) (τ : P semi-dec-str-up-to m)
        → F (semi-dec-limit-ordinal P n σ) (semi-dec-limit-ordinal P m τ))
  → F ((P characteristic-ordinal-up-to n) P-semi-dec↓)
      ((P characteristic-ordinal-up-to m) P-semi-dec↓)
 characteristic-ordinal-up-to-reduction-lemma₂ F F-is-prop {n} {m} hyp =
  ∥-∥rec
   (F-is-prop _ _)
   (λ σ →
     ∥-∥rec (F-is-prop _ _)
            (λ τ → subst2 F
                    (characteristic-ordinal-up-to-compatible P n P-semi-dec↓ σ)
                    (characteristic-ordinal-up-to-compatible P m P-semi-dec↓ τ)
                    (hyp σ τ))
            (Finite-Choice m P-semi-dec↓))
   (Finite-Choice n P-semi-dec↓)

 characteristic-ordinal-up-to-zero :
  (P characteristic-ordinal-up-to 0) P-semi-dec↓ ≡ ω
 characteristic-ordinal-up-to-zero =
  characteristic-ordinal-up-to-reduction-lemma
   (_≡ ω)
   (λ x → Brw-is-set x ω)
   (semi-dec-limit-ordinal-zero P)

 characteristic-ordinal-up-to-suc-bounded
  : (n : ℕ)
  → (P characteristic-ordinal-up-to (suc n)) P-semi-dec↓
    ≤ (P characteristic-ordinal-up-to n) P-semi-dec↓ + ω
 characteristic-ordinal-up-to-suc-bounded n =
  characteristic-ordinal-up-to-reduction-lemma₂
   (λ x y → x ≤ y + ω)
   (λ x y → ≤-trunc)
   (λ σ τ → semi-dec-limit-ordinal-bounded P n τ σ)

 characteristic-ordinal-up-to-bounded
  : (n : ℕ)
  → (P characteristic-ordinal-up-to n) P-semi-dec↓ ≤ ω · ι (suc n)
 characteristic-ordinal-up-to-bounded zero =
  subst ((P characteristic-ordinal-up-to 0) P-semi-dec↓ ≤_)
        (sym ω·1≡ω)
        (≤-refl-≡ characteristic-ordinal-up-to-zero)
 characteristic-ordinal-up-to-bounded (suc n) =
  ≤-trans (characteristic-ordinal-up-to-suc-bounded n)
          (+x-mono ω (characteristic-ordinal-up-to-bounded n))

 characteristic-ordinal-up-to-is-lim
  : (n : ℕ) → is-lim ((P characteristic-ordinal-up-to n) P-semi-dec↓)
 characteristic-ordinal-up-to-is-lim n =
  characteristic-ordinal-up-to-reduction-lemma
   is-lim
    (λ _ → isProp⟨is-lim⟩)
    (λ σ → is-lim-limit (ω-sequence P n σ) (ω-sequence-increasing P n σ))

 characteristic-ordinal-up-to-weakly-increasing
  : (n : ℕ)
  → (P characteristic-ordinal-up-to n) P-semi-dec↓
    ≤ (P characteristic-ordinal-up-to (suc n)) P-semi-dec↓
 characteristic-ordinal-up-to-weakly-increasing n =
  characteristic-ordinal-up-to-reduction-lemma₂ (_≤_)
   (λ x y → ≤-trunc)
   (semi-dec-limit-ordinal-increasing P n)

 characteristic-sequence : ℕ → Brw
 characteristic-sequence n =
  (P characteristic-ordinal-up-to n) (semi-dec-restrict-to n P-semi-dec) + ι n

 characteristic-sequence-increasing :
  increasing (characteristic-sequence)
 characteristic-sequence-increasing n =
  ≤∘<-in-<
   (+x-mono (ι n) (characteristic-ordinal-up-to-weakly-increasing n))
   (x+-mono-< {_} {ι n} ≤-refl)

 characteristic-ordinal : Brw
 characteristic-ordinal =
  limit characteristic-sequence {characteristic-sequence-increasing}

 characteristic-ordinal-bounded : characteristic-ordinal ≤ ω · ω
 characteristic-ordinal-bounded = simulation→≤ [1]
  where
   [1] : (k : ℕ)
       → Σ ℕ (λ n → characteristic-sequence k ≤ ω · ι n)
   [1] k = n , cancel-finite-lim-≤-left
                ((P characteristic-ordinal-up-to k) P-semi-dec↓)
                (ω · ι n)
                (characteristic-ordinal-up-to-is-lim k)
                (ω·sk-islim (suc k))
                k
                [2]
    where
     n = suc (suc k)
     [2] : (P characteristic-ordinal-up-to k) P-semi-dec↓ < ω · ι n
     [2] = ≤∘<-in-<
            (characteristic-ordinal-up-to-bounded k)
            (x·-mono-< {ω} lim≢zero (ι-mono-< {suc k} {n} N.<-suc))
