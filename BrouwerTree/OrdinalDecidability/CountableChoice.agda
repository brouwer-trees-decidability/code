{-# OPTIONS --cubical --erasure --guardedness  #-}
module BrouwerTree.OrdinalDecidability.CountableChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _N+_)
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥ renaming (⊥ to Empty)
open import Cubical.Relation.Nullary using (Dec; yes; no; isPropDec; decRec; ¬_)
open import Cubical.Relation.Nullary.Properties using (isProp¬)

open import PropTrunc
open import Iff
open import General-Properties

open import BrouwerTree.Everything

open import BrouwerTree.OrdinalDecidability.Basic
open import BrouwerTree.OrdinalDecidability.GeneralProperties
open import BrouwerTree.OrdinalDecidability.QuantificationTheorem
open import BrouwerTree.OrdinalDecidability.SierpinskiBelowOmegaSquared
open import BrouwerTree.OrdinalDecidability.Sierpinski

private
 variable
  ℓ ℓ' : Level

CC-implies-semidec-closed-under-countable-joins
 : CountableChoice ℓ → Semidecidable-Closed-Under-Countable-Joins ℓ
CC-implies-semidec-closed-under-countable-joins cc P _ σ =
 ∥-∥map (∃-semi-dec-str P) (cc σ)

CC→ω·n≤x-semi-dec : CountableChoice ℓ-zero
                  → (x : Brw) → (n : ℕ) → semi-dec (ω · ι n ≤ x)
CC→ω·n≤x-semi-dec cc x zero = ∣ dec→semi-dec ((ω · ι zero) ≤ x) (yes ≤-zero) ∣
CC→ω·n≤x-semi-dec cc x (suc n) = Brw-ind (λ x → semi-dec (ω · ι (suc n) ≤ x))
                                         (λ x → isPropPropTrunc)
                                         [1] [2] (λ {f} {f↑} → [3] {f↑ = f↑}) x
  where
   [1] : semi-dec (ω · ι (suc n) ≤ zero)
   [1] = ∣ dec→semi-dec _ (no lim≰zero) ∣
   [2] : {y : Brw} → semi-dec (ω · ι (suc n) ≤ y) → semi-dec (ω · ι (suc n) ≤ succ y)
   [2] {y} ih = rl (semi-dec-stable-under-↔ _ _ (lim≤sx↔lim≤x _ y)) ih
   [3] : {f : ℕ → Brw} {f↑ : increasing f}
       → ((k : ℕ) → semi-dec (ω · ι (suc n) ≤ f k))
       → semi-dec (ω · ι (suc n) ≤ limit f)
   [3] {f} {f↑} ih =
    rl (semi-dec-stable-under-↔ _ (∃[ m ∈ ℕ ] ω · ι n ≤ f m) [4]) [5]
     where
      [4] = ω · ι (suc n) ≤ limit f                ↔⟨ [4]₁ ⟩
            (∀ k → ∃[ m ∈ ℕ ] ω · ι n + ι k ≤ f m) ↔⟨ (λ f → f 0) , [4]₂ ⟩
            ∃[ m ∈ ℕ ] ω · ι n ≤ f m               ↔∎
       where
        [4]₁ = lim≤lim↔weakly-bisimilar (λ k → ω · ι n + ι k) f
        [4]₂ : ∃[ m ∈ ℕ ] ω · ι n ≤ f m → (∀ k → ∃[ m ∈ ℕ ] ω · ι n + ι k ≤ f m)
        [4]₂ l zero = l
        [4]₂ l (suc k) = ∥-∥map (λ (m , q) → (m N+ suc k ,
                                              ≤-offset-by-ι f {f↑} (ω · ι n) q)) l
      [5] : semi-dec (∃[ m ∈ ℕ ] ω · ι n ≤ f m)
      [5] = CC-implies-semidec-closed-under-countable-joins cc
             (λ m → ω · ι n ≤ f m)
             (λ m → isProp⟨≤⟩)
             (λ m → CC→ω·n≤x-semi-dec cc (f m) n)

CC-implies-ω·n-dec-is-semi-dec : CountableChoice ℓ-zero
                               → (P : Type ℓ)
                               → isProp P
                               → (k : ℕ)
                               → ordinal-dec (ω · ι k) P
                               → semi-dec P
CC-implies-ω·n-dec-is-semi-dec cc P P-prop k τ =
 ∥-∥rec isPropPropTrunc (uncurry [1]) τ
  where
   [1] : (x : Brw) → (P ↔ ω · ι k ≤ x) → semi-dec P
   [1] x ρ = rl (semi-dec-stable-under-↔ P _ ρ) (CC→ω·n≤x-semi-dec cc x k)

CC-implies-ω²-decidable-are-∀-of-semidecidable-props
 : CountableChoice ℓ-zero
 → (P : Type ℓ)
 → isProp P
 → ordinal-dec (ω · ω) P
 → ∃[ Q ∈ (ℕ → Type) ]
     ((n : ℕ) → isProp (Q n)) × ((n : ℕ) → semi-dec (Q n)) × ((∀ n → (Q n)) ↔ P)
CC-implies-ω²-decidable-are-∀-of-semidecidable-props cc P P-prop =
 ∥-∥rec isPropPropTrunc τ
  where
   τ : ordinal-dec-str (ω · ω) P → ∃[ Q ∈ (ℕ → Type) ] _
   τ (x , ρ) = ⊎.rec (∥-∥map τₗ) τ₀ (⇓-Islim⊎zero x)
    where
     τ₀ : ⇓ x ≡ zero →  ∃[ Q ∈ (ℕ → Type) ] _
     τ₀ ⇓x-zero = ∣ Q , (λ n → isProp⊥) , Q-semidec , Q-spec ∣
      where
       Q : ℕ → Type
       Q _ = Empty
       Q-semidec : (n : ℕ) → semi-dec (Q n)
       Q-semidec n = ∣ ⊥-semi-dec-str ∣
       Q-spec : (∀ n → Q n) ↔ P
       Q-spec = (λ q → ⊥.rec (q 17)) , λ p → ⊥.rec (limf≤⇓fin→⊥ x _ ⇓x-zero (lr ρ p))
     τₗ : is-Σlim (⇓ x) →  Σ[ Q ∈ (ℕ → Type) ] _
     τₗ ((g , g↑) , ⇓x-lim) = Q , (λ n → isPropPropTrunc) , Q-semidec , Q-spec
       where
        Q : ℕ → Type
        Q n = ∃[ m ∈ ℕ ] ω · ι n ≤ g m
        Q-semidec : (n : ℕ) → semi-dec (Q n)
        Q-semidec n = CC-implies-semidec-closed-under-countable-joins cc
                       (λ k → ω · ι n ≤ g k)
                       (λ k → isProp⟨≤⟩)
                       (λ k → CC→ω·n≤x-semi-dec cc (g k) n)
        Q-spec = ↔-sym (P            ↔⟨ ρ ⟩
                        ω · ω ≤ x   ↔⟨ lim≤x↔lim≤⇓x x (λ n → ω · ι n) ⟩
                        ω · ω ≤ ⇓ x ↔⟨ [1] ⟩
                        (∀ n → Q n)  ↔∎)
         where
          [1] = subst (λ z → ω · ω ≤ z ↔((n : ℕ) → Q n))
                      (sym (is-lim→≡limit {f↑ = g↑} ⇓x-lim))
                      (lim≤lim↔weakly-bisimilar (λ n → ω · ι n) g)

∀∀-ω²dec : (Q : ℕ → ℕ → Type ℓ)
         → (∀ (m n : ℕ) → semi-dec (Q m n))
         → (∀ (m n : ℕ) → isProp (Q m n))
         → ordinal-dec (ω · ω) (∀ (m n : ℕ) → Q m n)
∀∀-ω²dec {ℓ} Q Q-semi-dec Q-is-prop =
 lr (ordinal-dec-stable-under-↔ (∀ (n : ℕ) → P n) (∀ (m n : ℕ) → Q m n) [2])
    ∣ Pₙ-ωdec→∀nPₙ-ω²dec P
       (λ k → Q-is-prop (fst (ϕ k)) (snd (ϕ k)))
       (λ k → Q-semi-dec (fst (ϕ k)) (snd (ϕ k))) ∣
  where
   open import Cubical.Data.Nat.Bijections.Product
   open import Cubical.Foundations.Isomorphism
   ϕ : ℕ → ℕ × ℕ
   ϕ = Iso.inv (ℕ×ℕ≅ℕ)
   ψ : ℕ × ℕ → ℕ
   ψ = Iso.fun (ℕ×ℕ≅ℕ)

   P : ℕ → Type ℓ
   P k = Q (fst (ϕ k)) (snd (ϕ k))
   [1] : (m n : ℕ) → P (ψ (m , n)) ≡ Q m n
   [1] m n = cong₂ Q (cong fst (Iso.ret ℕ×ℕ≅ℕ (m , n)))
                     (cong snd (Iso.ret ℕ×ℕ≅ℕ (m , n)))
   [2] : ((n : ℕ) → P n) ↔ ((m n : ℕ) → Q m n)
   [2] = (λ p m n → transport ([1] m n) (p (ψ (m , n)))) ,
         (λ q k → q (fst (ϕ k)) (snd (ϕ k)))

CC-implies-ω²-dec-closed-under-∀
 : CountableChoice (ℓ-max (ℓ-suc ℓ-zero) ℓ)
 → (P : ℕ → Type ℓ)
 → ((n : ℕ) → isProp (P n))
 → (( n : ℕ ) → ordinal-dec (ω · ω) (P n))
 → ordinal-dec (ω · ω) (∀ n → P n)
CC-implies-ω²-dec-closed-under-∀ cc P P-prop σ =
 ∥-∥rec isPropPropTrunc τ (cc ∥Q∥)
  where
   ∥Q∥ : (m : ℕ) → ∃[ Q ∈ (ℕ → Type) ]
                     ((n : ℕ) → isProp (Q n)) ×
                     ((n : ℕ) → semi-dec (Q n)) ×
                     ((∀ n → (Q n)) ↔ (P m))
   ∥Q∥ m = CC-implies-ω²-decidable-are-∀-of-semidecidable-props (CC-lower cc)
                                                                (P m)
                                                                (P-prop m)
                                                                (σ m)

   τ : ((m : ℕ) → Σ[ Q ∈ (ℕ → Type) ] _) → ordinal-dec (ω · ω)  (∀ n → P n)
   τ H = lr (ordinal-dec-stable-under-↔ _ _ Q-spec) (∀∀-ω²dec Q Q-semidec Q-prop)
    where
     Q : ℕ → ℕ → Type
     Q n m = fst (H n) m
     Q-prop : (n m : ℕ) → isProp (Q n m)
     Q-prop n m = fst (snd (H n)) m
     Q-semidec : (n m : ℕ) → semi-dec (Q n m)
     Q-semidec n m = fst (snd (snd (H n))) m
     Q-spec : (∀ m n → Q m n) ↔ (∀ m → P m)
     Q-spec = (λ h m → lr (snd (snd (snd (H m)))) (h m)) ,
              (λ h m n → rl (snd (snd (snd (H m)))) (h m) n)


CC-implies-𝕊-eq-is-semidec
 : CountableChoice ℓ-zero
 → (x : 𝕊)
 → semi-dec (x ≡ ⊤)
CC-implies-𝕊-eq-is-semidec cc =
 𝕊-ind (λ x → semi-dec (x ≡ ⊤))
 (λ x → isPropPropTrunc)
 ∣ dec→semi-dec (⊤ ≡ ⊤) (yes refl) ∣
 ∣ dec→semi-dec (⊥ ≡ ⊤) (no ⊥≠⊤) ∣
 λ {s} ih → ∥-∥rec isPropPropTrunc
                   (λ σ → rl (semi-dec-stable-under-↔ _ _ (is-⊤↔contains-⊤ s))
                             (CC-implies-semidec-closed-under-countable-joins
                               cc
                               (λ n → s n ≡ ⊤)
                               (λ n → isSet𝕊 _ _)
                               ih))
                    (cc ih)

CC-implies-semidec-and-𝕊-dec-coincide
 : CountableChoice ℓ-zero
 → (P : Type ℓ)
 → isProp P
 → semi-dec P ↔ 𝕊-dec P
CC-implies-semidec-and-𝕊-dec-coincide cc P P-prop = semidec→𝕊-dec P P-prop , ρ
 where
  ρ : 𝕊-dec P → semi-dec P
  ρ (y , σ) = rl (semi-dec-stable-under-↔ _ _ σ) (CC-implies-𝕊-eq-is-semidec cc y)


ω²-collapse-implies-semidecidable-closed-under-negation
 : (∀ {ℓ} (P : Type ℓ) → isProp P → ordinal-dec (ω · ω) P → semi-dec P)
 → (P : Type ℓ') → semi-dec P → semi-dec (¬ P)
ω²-collapse-implies-semidecidable-closed-under-negation h P σ =
 ∥-∥rec isPropPropTrunc [1] σ
  where
   [1] : semi-dec-str P → semi-dec (¬ P)
   [1] (s , ρ) = h (¬ P) (isProp¬ P) [3]'
    where
     [2]₁ : (∀ n → s n ≡ false) → ¬ P
     [2]₁ h p = ∥-∥rec isProp⊥ (λ (n , e) → true≢false (sym e ∙ h n)) (lr ρ p)
     [2]₂ : ¬ P → (∀ n → s n ≡ false)
     [2]₂ ¬p n = ¬true→false (s n) λ e → ¬p (rl ρ ∣ n , e ∣ )
     [3] : ordinal-dec (ω · ω) (∀ n → s n ≡ false)
     [3] = ∣ Pₙ-ωdec→∀nPₙ-ω²dec (λ n → s n ≡ false)
                                 (λ n → isSetBool _ _)
                                 (λ n → ∣ dec→semi-dec _ (s n ≟ false) ∣) ∣
     [3]' : ordinal-dec (ω · ω) (¬ P)
     [3]' = lr (ordinal-dec-stable-under-↔ _ _ ([2]₁ , [2]₂)) [3]

semi-dec-Dec : (P : Type ℓ)
             → isProp P
             → semi-dec P
             → semi-dec (¬ P)
             → semi-dec (Dec P)
semi-dec-Dec P P-prop σ σ' =
 lr (semi-dec-stable-under-↔ _ _ ([1] , [2])) (∨-semi-dec _ _ σ σ')
  where
   [1] : ∥ P ⊎ (¬ P) ∥ → Dec P
   [1] = ∥-∥rec (isPropDec P-prop) (⊎.rec yes no)
   [2] : Dec P → ∥ P ⊎ (¬ P) ∥
   [2] = ∣_∣ ∘ decRec inl inr

MP-and-semidecidable-closed-under-negation-imply-LPO
 : MP
 → (∀ {ℓ} → (P : Type ℓ) → isProp P → semi-dec P → semi-dec (¬ P))
 → LPO
MP-and-semidecidable-closed-under-negation-imply-LPO mp h = LPO'→LPO [1]
 where
  [1] : LPO' ℓ-zero
  [1] P P-prop σ = MP→MP' mp (Dec P) (isPropDec P-prop) [2] [3]
   where
    [2] : semi-dec (Dec P)
    [2] = semi-dec-Dec P P-prop σ (h P P-prop σ)
    [3] : ¬ (¬ Dec P)
    [3] ¬d = ¬d (no λ p → ¬d (yes p))

-- Above, we proved that Countable Choice implies that
-- ω·k-decidability collapses to semi-decidability for all k. However
-- countable choice does not make the whole hierarchy of
-- α-decidability collapse: Since there are models where Countable
-- Choice and Markov's Principle holds, but LPO does not [1], the
-- following shows that Countable Choice does not prove that all
-- ω²-decidable propositions are semi-decidable.

-- [1] "Separating Fragments Of {WLEM}, {LPO}, and {MP}"
--     Matt Hendtlass and Robert Lubarsky
--     The Journal of Symbolic Logic 81(4), 2016, pp. 1315–1343
--     https://doi.org/10.1017/jsl.2016.38

MP-and-ω²-collapse-imply-LPO
 : MP
 → (∀ {ℓ} (P : Type ℓ) → isProp P → ordinal-dec (ω · ω) P → semi-dec P)
 → LPO
MP-and-ω²-collapse-imply-LPO mp ω²-collapse =
 MP-and-semidecidable-closed-under-negation-imply-LPO mp
  (λ P _ → ω²-collapse-implies-semidecidable-closed-under-negation ω²-collapse P)


{-

-- Old proofs below, delete once we are sure there is nothing additional in it

-- Theorem: Assuming Countable choice, each ω·(k+2)-decidable proposition is ω·2-decidable (semidecidable).
-- First we prove it for k=1:
-- Theorem : Countable choice implies that each ω·3-decidable proposition is semidecidable:

side1 : (f : ℕ → Brw) → {f↑ : increasing f}
      → (⇓data : (k : ℕ) → (ℕ → Brw)) → (⇓-incr : (k : ℕ) → increasing (⇓data k))
      → ((k : ℕ) → ((⇓ (f k) ≡ limit (⇓data k) {⇓-incr k})
         ⊎ ((⇓ (f k) ≡ zero) × (⇓data k ≡ ι) )))
      →  ((ω + ω) + ω ≤ limit f {f↑}) →  ∃[ k ∈ ℕ ] Σ[ k' ∈ ℕ ] ω ≤ ⇓data k k'
side1 f {f↑} ⇓data ⇓-incr ⇓-equ hypothesis =
 ∥-∥rec isPropPropTrunc snd-step fst-step
  where
    ⇓-impossible : (x : Brw) → (⇓ x ≡ zero) → ω ≤ x → ⊥
    ⇓-impossible x p q = lim≰zero (≤-trans (⇓-monotone x ω q) (≤-refl-≡ p))

    h-cor : ∃[ k ∈ ℕ ] ω + ω ≤ f k
    h-cor = lim≤lim→weakly-bisimilar (λ u → (ω + ω) + ι u) f hypothesis 0
    fst-step : ∃[ k ∈ ℕ ] ω + ω ≤ limit (⇓data k) {⇓-incr k}
    fst-step = ∥-∥rec isPropPropTrunc helper h-cor
      where
       helper : Σ[ k ∈ ℕ ] ω + ω ≤ f k
              → ∃[ k ∈ ℕ ] ω + ω ≤ limit (⇓data k) {⇓-incr k}
       helper (k , hk) = ∣ k ,
                      sumrec (λ h2 → subst (λ z → ω + ω ≤ z ) h2
                      ((lim≤x→lim≤⇓x (f k) (λ n → ω + ι n) hk)) )
                      (λ (p1 , q1) → ⊥.rec (⇓-impossible (f k) p1
                      (≤-trans (ω-smallest (λ n → ω + ι n)) hk))) (⇓-equ k) ∣
    snd-step : Σ[ k ∈ ℕ ] ω + ω ≤ limit (⇓data k) {⇓-incr k}
             → ∃[ k ∈ ℕ ] Σ[ k' ∈ ℕ ] ω ≤ ⇓data k k'
    snd-step (k , hk) = ∥-∥rec isPropPropTrunc (λ b → ∣ k , b ∣)
                        (lim≤lim→weakly-bisimilar (λ u → ω + ι u) (⇓data k) hk zero)

side2 : (f : ℕ → Brw) → {f↑ : increasing f}
       → (⇓data : (k : ℕ) → (ℕ → Brw)) → (⇓-incr : (k : ℕ) → increasing (⇓data k))
       → ((k : ℕ) → ((⇓ (f k) ≡ limit (⇓data k) {⇓-incr k})
         ⊎ ((⇓ (f k) ≡ zero) × (⇓data k ≡ ι) )))
       → ∃[ k ∈ ℕ ] Σ[ k' ∈ ℕ ] ω ≤ ⇓data k k'
       → (ω + ω) + ω ≤ limit f {f↑}
side2 f {f↑} ⇓data ⇓-incr ⇓-equ hypothesis =
 weakly-bisimilar→lim≤lim (λ n → (ω + ω) + ι n) f
 (λ k → ∥-∥rec isPropPropTrunc (snd-fun k) fst-step)
  where
    fst-fun : Σ[ k ∈  ℕ ] ∃[ k' ∈ ℕ ] ω ≤ ⇓data k k'
             → ∃[ k ∈ ℕ ] ω + ω ≤ limit (⇓data k) {⇓-incr k}
    fst-fun (k , hk) = ∣ k , weakly-bisimilar→lim≤lim (λ n → ω + ι n) (⇓data k)
                       (λ u → ∥-∥rec isPropPropTrunc (helper u) hk) ∣
      where
        helper : (u : ℕ)
               → Σ[ k' ∈ ℕ ] ω ≤ ⇓data k k' → ∃[ n ∈ ℕ ] ω + ι u ≤ ⇓data k n
        helper u  (k' , hk') = ∣ k' N+ u , ≤-trans
                               (+-mono {y = ι u}{y' = ι u} hk' ≤-refl)
                               (add-finite-part-lemma' (⇓data k) {⇓-incr k} k' u) ∣
    fst-step' : ∃[ k ∈ ℕ ] ω + ω ≤ limit (⇓data k) {⇓-incr k}
    fst-step' = ∥-∥rec isPropPropTrunc fst-fun
                (∥-∥rec isPropPropTrunc (λ (k , b) → ∣ k , ∣ b ∣ ∣) hypothesis)
    helper2 : Σ[ k ∈ ℕ ] ω + ω ≤ limit (⇓data k) {⇓-incr k}
            → ∃[ k ∈ ℕ ] ω + ω ≤ f k
    helper2 (k , hk) = ∣ k ,
                       ≤-trans (subst (λ z → ω + ω ≤ z)
                               (Cubical.Data.Sum.rec (λ p → sym p)
                       (λ (p , q) → ⊥.rec (ω·2≮ω (subst (λ z → ω + ω ≤ z)
                       (limit-pointwise-equal (⇓data k)
                         ι (λ n → funExt⁻ q n)) hk)))
                       (⇓-equ k)) hk) (⇓x≤x (f k)) ∣
    fst-step :  ∃[ k ∈ ℕ ] ω + ω ≤ f k
    fst-step =  ∥-∥rec isPropPropTrunc helper2 fst-step'
    snd-fun : (u : ℕ) → Σ[ k ∈ ℕ ] ω + ω ≤ f k → ∃[ k ∈ ℕ ] (ω + ω) + ι u  ≤ f k
    snd-fun u (k , hk) = ∣ k N+ u , ≤-trans (+-mono {y = ι u}{y' = ι u} hk ≤-refl)
                           (add-finite-part-lemma' f {f↑} k u) ∣

-----------
∃∃semidec : (f : ℕ → ℕ → Brw) → semi-dec (∃[ k ∈ ℕ ] Σ[ k' ∈ ℕ ] ω ≤ f k k')
∃∃semidec f = ∃∃dec-is-semidec (λ z k' → ω ≤ f z k')
 (λ n m → dec↔ω-dec (ω ≤ f n m) ≤-trunc .snd ∣ f n m , (λ - → -) , (λ - → -) ∣)
-----------
corollary : (f : ℕ → Brw) → {f↑ : increasing f}
            → (⇓data : (k : ℕ) → (ℕ → Brw)) → (⇓-incr : (k : ℕ) → increasing (⇓data k))
            → ((k : ℕ) → ((⇓ (f k) ≡ limit (⇓data k) {⇓-incr k})
              ⊎ ((⇓ (f k) ≡ zero) × (⇓data k ≡ ι) )))
            → (semi-dec ((ω + ω) + ω ≤ limit f {f↑}))
corollary f {f↑} ⇓data ⇓-incr ⇓-equ  = semi-dec-stable-under-↔
            (∃[ k ∈ ℕ ] Σ[ k' ∈ ℕ ] ω ≤ ⇓data k k')
            ((ω + ω) + ω ≤ limit f {f↑}) ((side2 f ⇓data ⇓-incr λ k → ⇓-equ k) ,
                                          (side1 f ⇓data ⇓-incr λ k → ⇓-equ k))
                                          .fst (∃∃semidec ⇓data)
----------
corollary-truncated : (f : ℕ → Brw) → {f↑ : increasing f} →
                      (∥ ( ∀ (k : ℕ) → (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g)
                      (λ g↑ → (⇓ (f k) ≡ limit g {g↑})  ⊎ ((⇓ (f k) ≡ zero) × (g ≡ ι) ))))))  ∥)
                      → (semi-dec ((ω + ω) + ω ≤ limit f {f↑}))

corollary-truncated f {f↑} h = ∥-∥rec PropTrunc.isPropPropTrunc helper h
   where
     helper :  ( ∀ (k : ℕ) → (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g)
                                        (λ g↑ →  (⇓ (f k) ≡ limit g {g↑})  ⊎ ((⇓ (f k) ≡ zero) × (g ≡ ι) ))))))
                      →  (semi-dec ((ω + ω) + ω ≤ limit f {f↑}))
     helper ⇓Data  = corollary f (λ k → (⇓Data k) .fst) (λ k → (⇓Data k) .snd .fst)
                                  λ k → (⇓Data k) .snd .snd

-----------------------------

⇓data-raw :  (f : ℕ → Brw) → {f↑ : increasing f} → (k : ℕ) → is-lim (⇓ (f k)) ⊎ (⇓ (f k) ≡ zero)
⇓data-raw f k = ⇓-Islim⊎zero (f k)

⇓data-first :  (f : ℕ → Brw) → {f↑ : increasing f} →  ∀ (k : ℕ) → ∥ (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g)
                               (λ g↑ → ( ⇓ (f k) ≡ limit g {g↑} ))))) ∥ ⊎ (⇓ (f k) ≡ zero)

⇓data-first f {f↑}  k = Cubical.Data.Sum.rec (λ p → inl (∥-∥rec PropTrunc.isPropPropTrunc helper p)) (λ p → inr p) (⇓data-raw f {f↑} k)
     where
        helper :  is-Σlim (⇓ (f k)) →  ∃[ g ∈ (ℕ → Brw) ] Σ[ g↑ ∈ (increasing g) ] ⇓ (f k) ≡ limit g {g↑}
        helper (F , hF)  = ∣ (F .fst) , (F .snd) , (is-lim→≡limit hF) ∣


⇓data-trunc-1 : (f : ℕ → Brw) → {f↑ : increasing f} →  ∀ (k : ℕ) → ∥ (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g)
                                                (λ g↑ → ( ⇓ (f k) ≡ limit g {g↑} ))))) ⊎ (⇓ (f k) ≡ zero) ∥
⇓data-trunc-1 f {f↑} k = helper (⇓data-first f {f↑} k)
     where
        helper :   ∥ (Σ (ℕ → Brw) (λ g → (Σ (increasing g)  (λ g↑ → ( ⇓ (f k) ≡ limit g {g↑} ))))) ∥ ⊎ (⇓ (f k) ≡ zero) →
                   ∥ (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g) (λ g↑ → ( ⇓ (f k) ≡ limit g {g↑} ))))) ⊎ (⇓ (f k) ≡ zero) ∥

        helper = Cubical.Data.Sum.rec (∥-∥map (λ - → inl - ))
                                      λ - → ∣ inr -  ∣

⇓data-trunc :  (f : ℕ → Brw) → {f↑ : increasing f} →
                  ∀ (k : ℕ) → ∥ (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g)
                                                (λ g↑ → ( ⇓ (f k) ≡ limit g {g↑} )  ⊎ ((⇓ (f k) ≡ zero) × (g ≡ ι) ))))) ∥

⇓data-trunc f {f↑} k = ∥-∥rec PropTrunc.isPropPropTrunc (Cubical.Data.Sum.rec (λ (G , hG) → ∣ G , (hG .fst) , inl (hG .snd) ∣)
                       λ p → ∣ ι , (ι-increasing , (inr (p , refl))) ∣) (⇓data-trunc-1 f {f↑} k)

---------------------------------------------

CC→ω·3dec-is-semidec-lemma :  CountableChoice → (f : ℕ → Brw) → {f↑ : increasing f} →
                          (semi-dec ((ω + ω) + ω ≤ limit f {f↑}))

CC→ω·3dec-is-semidec-lemma cc f {f↑} = corollary-truncated f (cc {A = λ k → [1] k} λ k → ⇓data-trunc f {f↑} k)
   where
     [1] : ℕ → Type
     [1] k = Σ (ℕ → Brw)
          (λ g →
          Σ (increasing g)
          (λ g↑ → (⇓ (f k) ≡ limit g {g↑}) ⊎ ((⇓ (f k) ≡ zero) × (g ≡ ι))))



CC→ω·3dec-is-semidec-lemma2 :  CountableChoice → (x : Brw) → (is-lim (x) ⊎ (x ≡ zero)) → (semi-dec ((ω + ω) + ω ≤ x))
CC→ω·3dec-is-semidec-lemma2 cc x h  = Cubical.Data.Sum.rec (∥-∥rec PropTrunc.isPropPropTrunc [1])
                                      ((λ p →  ∣ dec→semi-dec (((ω + ω) + ω) ≤ x) (no (λ q → lim≰zero (≤-trans q (≤-refl-≡ p)) )) ∣)) h

       where
          [1] = (λ (F , hF) → subst (λ z → semi-dec ((ω + ω) + ω ≤ z)) (sym (is-lim→≡limit hF))
                                                                     (CC→ω·3dec-is-semidec-lemma cc (F .fst) {F .snd})) --ok

CC→ω·3dec-is-semidec :  CountableChoice → (P : Type ℓ) → (ordinal-dec ((ω + ω) + ω) P) → semi-dec P
CC→ω·3dec-is-semidec cc P P-orddec = ∥-∥rec PropTrunc.isPropPropTrunc (λ (F , hF) → (semi-dec-stable-under-↔ (((ω + ω) + ω) ≤ ⇓ F) P
                                     ((λ p → hF .snd (≤-trans p (⇓x≤x F))) , λ p → lim≤x→lim≤⇓x F (λ n → (ω + ω) + ι n) (hF .fst p)))
                                     .fst
                                     (CC→ω·3dec-is-semidec-lemma2 cc (⇓ F) (⇓-Islim⊎zero F))) P-orddec

--------------------------------------------------
--Theorem : Countable choice implies that each ω·(k+2)-decidable is semidecidable.

---------------------------------------------------

main-side1 : (f : ℕ → Brw) → {f↑ : increasing f} → (k : ℕ)
           → (ω · ι k + ω) + ω ≤ limit f {f↑}
           → ∃[ u ∈ ℕ ] ω · ι k + ω ≤ ⇓ (f u)
main-side1 f {f↑} k p = ∥-∥rec PropTrunc.isPropPropTrunc (λ (n , hn) → ∣ n , lim≤x→lim≤⇓x (f n) (λ n₁ → ω · ι k + ι n₁) hn ∣)
                        (lim≤lim→weakly-bisimilar (λ u → (ω · ι k + ω) + ι u) f p zero)

main-side2 : (f : ℕ → Brw) → {f↑ : increasing f}  → (k : ℕ)
           →  ∃[ u ∈ ℕ ] ω · ι k + ω ≤ ⇓ (f u)
           →  (ω · ι k + ω) + ω ≤ limit f {f↑}
main-side2 f {f↑} k p = ∥-∥rec ≤-trunc (λ (n , hn) → simulation→≤ (λ u → n N+ u ,
                       ≤-trans (+-mono {y = ι u} {y' = ι u} (≤-trans hn (⇓x≤x (f n))) ≤-refl) (add-finite-part-lemma' f {f↑} n u)))
                       p

---------------------------------------------------

CC→ω·k+2dec-is-semidec-lemma : CountableChoice → (k : ℕ)
                             → (f : ℕ → Brw) → {f↑ : increasing f}
                             → (semi-dec ((ω · ι k + ω) + ω ≤ limit f {f↑}))
CC→ω·k+2dec-is-semidec-lemma cc zero f {f↑} = ω·2dec→semidec (((ω · ι zero + ω) + ω) ≤ limit f) ≤-trunc
                                             ∣ limit f , (λ p → ≤-trans (≤-refl-≡ (cong (λ z → z + ω)
                                             (sym ω·1≡ω))) p)
                                             , (λ p → ≤-trans (≤-refl-≡ (cong(λ z → z + ω) ω·1≡ω)) p) ∣
CC→ω·k+2dec-is-semidec-lemma cc (suc k) f {f↑} = lr (semi-dec-stable-under-↔ (∃[ u ∈ ℕ ] ω · ι (suc k) + ω ≤ ⇓ (f u))
                                                                              ((ω · ι (suc k) + ω) + ω ≤ limit f)
                                                                              (main-side2 f (suc k) , main-side1 f (suc k)))
                                                    [UseIH]
  where
     [UseIH] : semi-dec (∃[ u ∈ ℕ ] ω · ι (suc k) + ω ≤ ⇓ (f u))
     [UseIH] = CC→ω·3dec-is-semidec cc (∃[ u ∈ ℕ ] ω · ι (suc k) + ω ≤ ⇓ (f u))
        ∣ (Pₙ-ωdec→∃nPₙ-ω·3dec (λ u → (ω · ι (suc k) + ω) ≤ ⇓ (f u)) (λ n → ≤-trunc)
        (λ v → IH-Cor v)) ∣
          where
            IH-Cor : (u : ℕ) → semi-dec ((ω · ι (suc k) + ω) ≤ ⇓ (f u))

            [goodData] :  (∥ ( ∀ (k : ℕ) → (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g)
                         (λ g↑ → (⇓ (f k) ≡ limit g {g↑})  ⊎ ((⇓ (f k) ≡ zero) × (g ≡ ι) ))))))  ∥)
            [goodData] =  (cc {A = λ k → [1] k} λ k → ⇓data-trunc f {f↑} k)
                 where
                    [1] : ℕ → Type
                    [1] k = Σ (ℕ → Brw) (λ g →  Σ (increasing g)
                                        (λ g↑ → (⇓ (f k) ≡ limit g {g↑}) ⊎ ((⇓ (f k) ≡ zero) × (g ≡ ι))))
            IH-Cor u  = ∥-∥rec PropTrunc.isPropPropTrunc [goodMap] [goodData]
               where
                [goodMap] : ( ∀ (k : ℕ) → (Σ (ℕ → Brw) (λ g →  (  Σ (increasing g)
                         (λ g↑ → (⇓ (f k) ≡ limit g {g↑})  ⊎ ((⇓ (f k) ≡ zero) × (g ≡ ι) ))))))
                         →  semi-dec ((ω · ι (suc k) + ω) ≤ ⇓ (f u))
                [goodMap] ⇓Data = Cubical.Data.Sum.rec
                                (λ p → subst (λ z → semi-dec (ω · ι (suc k) + ω ≤ z)) (sym p) IH')
                 (λ (p , q) → ∣ dec→semi-dec ((ω · ι (suc k) + ω) ≤ ⇓ (f u))
                 (no (λ w → lim≰zero (≤-trans w (≤-refl-≡ p)))) ∣)
                                     (((⇓Data u) .snd .snd))
                  where
                    IH : semi-dec (((ω · ι k + ω) + ω) ≤ limit (⇓Data u .fst))
                    IH = CC→ω·k+2dec-is-semidec-lemma cc k ((⇓Data u) .fst) {((⇓Data u) .snd .fst)}
                    IH' : semi-dec ((ω · ι (suc k) + ω) ≤ limit (⇓Data u .fst) {⇓Data u .snd .fst})
                    IH' = subst (λ z → semi-dec ((z + ω) ≤ limit (⇓Data u .fst) {⇓Data u .snd .fst}))
                        (refl) IH

----

CC→ω·k+2dec-is-semidec-lemma2 :  CountableChoice → (k : ℕ) → (x : Brw) → (is-lim (x) ⊎ (x ≡ zero)) → (semi-dec ((ω · ι k + ω) + ω ≤ x))
CC→ω·k+2dec-is-semidec-lemma2 cc k x h  = Cubical.Data.Sum.rec (∥-∥rec PropTrunc.isPropPropTrunc [1])
                                      ((λ p →  ∣ dec→semi-dec ((ω · ι k + ω) + ω ≤ x) (no (λ q → lim≰zero (≤-trans q (≤-refl-≡ p)) )) ∣)) h

       where
          [1] = (λ (F , hF) → subst (λ z → semi-dec ((ω · ι k + ω) + ω ≤ z)) (sym (is-lim→≡limit hF))
                                                                     (CC→ω·k+2dec-is-semidec-lemma cc k (F .fst) {F .snd})) --ok

CC→ω·k+2dec-is-semidec :  CountableChoice → (k : ℕ) → (P : Type ℓ) → (ordinal-dec ((ω · ι k + ω) + ω) P) → semi-dec P
CC→ω·k+2dec-is-semidec cc k P P-orddec = ∥-∥rec PropTrunc.isPropPropTrunc (λ (F , hF) → (semi-dec-stable-under-↔ (((ω · ι k + ω) + ω) ≤ ⇓ F) P
                                     ((λ p → hF .snd (≤-trans p (⇓x≤x F))) , λ p → lim≤x→lim≤⇓x F (λ n → (ω · ι k + ω) + ι n) (hF .fst p)))
                                     .fst
                                     (CC→ω·k+2dec-is-semidec-lemma2 cc k (⇓ F) (⇓-Islim⊎zero F))) P-orddec
-}
