{-# OPTIONS --cubical --erasure --guardedness --lossy-unification #-}
module BrouwerTree.OrdinalDecidability.Paper where

open import BrouwerTree.OrdinalDecidability.Basic
open import BrouwerTree.OrdinalDecidability.GeneralProperties
open import BrouwerTree.OrdinalDecidability.MinFunctionRel
open import BrouwerTree.OrdinalDecidability.MaxFunctionRel
open import BrouwerTree.OrdinalDecidability.QuantificationConstruction
open import BrouwerTree.OrdinalDecidability.QuantificationCut
open import BrouwerTree.OrdinalDecidability.QuantificationLemmas
open import BrouwerTree.OrdinalDecidability.QuantificationTheorem
open import BrouwerTree.OrdinalDecidability.LPOMinMax
open import BrouwerTree.OrdinalDecidability.CountableChoice
open import BrouwerTree.OrdinalDecidability.Sierpinski
open import BrouwerTree.OrdinalDecidability.SierpinskiBelowOmegaSquared

open import BrouwerTree.Everything

open import Cubical.Data.Bool as B using (Bool)
open import Cubical.Data.Empty.Properties
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _N+_)
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import General-Properties
open import Iff
open import PropTrunc
open import FinChoice

private
 variable
  ℓ : Level

-- Section 2. Brouwer ordinals

module Lemma-2-1 where
 [1] : (α : Brw)
     → (α ≡ zero)
       ⊎ ((Σ[ β ∈ Brw ] α ≡ succ β)
       ⊎ (∃[ f ∈ (ℕ → Brw) ] Σ[ f↑ ∈ increasing f ] α ≡ limit f {f↑}))
 [1] α = lem (Brw-has-classification α)
  where
   lem : is-zero α ⊎ (is-strong-suc α ⊎ is-lim α)
       → (α ≡ zero)
         ⊎ ((Σ[ β ∈ Brw ] α ≡ succ β)
         ⊎ (∃[ f ∈ (ℕ → Brw) ] Σ[ f↑ ∈ increasing f ] α ≡ limit f {f↑}))
   lem (inl z) = inl (is-zero→≡zero z)
   lem (inr (inl (β , s , _))) = inr (inl (β , is-suc→≡succ s))
   lem (inr (inr l)) =
    inr (inr (∥-∥map (λ ((f , f↑) , l') → (f , f↑ , is-lim→≡limit l')) l))

 [2] : (α : Brw)
     → (α < ω) ⊎ (ω ≤ α)
     × (α < ω → Σ[ n ∈ ℕ ] ι n ≡ α)
 [2] α = (<ω-or-≥ω α , lr (isFinite-correct' α) ∘ rl (isFinite-correct₂ α))

 [2]-ad : (((α β : Brw) → Dec (α ≤ β)) ↔ LPO)
        × (((α β : Brw) → Dec (α ≡ β)) ↔ LPO)
 [2]-ad = ((λ h → Decω<→LPO (λ β → h (succ ω) β)) , LPO→Dec≤) ,
          ((λ h → Dec≡ω·2→LPO (λ β → h β (ω + ω))) , LPO→Dec≡)

 [3] : BinaryRelation.isTrans _<_
     × isWellFounded _<_
     × ((α β : Brw) → (∀ γ → (γ < α) ↔ (γ < β)) → α ≡ β)
 [3] = <-trans , <-is-wellfounded , <-extensional

 [4] : (α β : Brw) → succ α ≤ succ β ↔ α ≤ β
 [4] _ _ = ≤-succ-mono⁻¹ , ≤-succ-mono

 [5] : (α : Brw) (f : ℕ → Brw) {f↑ : increasing f}
     → α < limit f {f↑} → ∃[ n ∈ ℕ ] α < f n
 [5] = below-limit-lemma

 [6] : (α : Brw) (f : ℕ → Brw) {f↑ : increasing f}
     → (limit f {f↑} ≤ succ α → limit f {f↑} ≤ α)
     × (α < limit f {f↑} → succ α < limit f {f↑})
 [6] α f = lim≤sx→lim≤x f α , x<lim→sx<lim f α

 [7] : (f g : ℕ → Brw) {f↑ : increasing f} {g↑ : increasing g}
     → limit f {f↑} ≤ limit g {g↑} → f ≲ g
 [7] f g = lim≤lim→weakly-bisimilar f g


Lemma-2-2 : (α β : Brw) → α ≤ β → (⇑ α ≤ ⇑ β) × (⇓ α ≤ ⇓ β)
Lemma-2-2 α β l = ⇑-monotone α β l , ⇓-monotone β α l

Lemma-2-3 : (α : Brw)
          → Σ[ ƛ ∈ Brw ] Σ[ n ∈ ℕ ] (α ≡ ƛ + ι n) × Brw-zero-or-limit ƛ
Lemma-2-3 α = ⇓ α , finite-part α , decompose-⇓-fin α , ⇓-Islim⊎zero α

module Lemma-2-4
        (ƛ : Brw)
        (ƛ-zl : Brw-zero-or-limit ƛ)
        (α : Brw)
       where

 [1] : α ≤ ƛ ↔ ⇑ α ≤ ƛ
 [1] = ⇑-left-≤ ƛ ƛ-zl α

 [2] : ƛ ≤ α ↔ ƛ ≤ ⇓ α
 [2] = ⇓-right-≤ ƛ ƛ-zl α

 [3] : ƛ < α ↔ ƛ < ⇑ α
 [3] = ⇑-right-≤ ƛ ƛ-zl α

-- Section 3. Ordinal Decidability and the Connection with Existing Notions

Definition-3-1 : Brw → Type ℓ → Type ℓ
Definition-3-1 = ordinal-dec

Proposition-3-2 : (P : Type ℓ) → isProp P
                → (Dec P      ↔ ordinal-dec (ι 1)     P)
                × (semi-dec P ↔ ordinal-dec (ω + ι 1) P)
Proposition-3-2 P Pprop = dec↔1-dec P Pprop , semidec↔ω+1-dec P Pprop

Definition-3-3 : ((ℕ → Bool) → (ℕ → Brw))
               × ((ℕ → Brw)  → (ℕ → Bool))
Definition-3-3 = jumpSeq
                 , (λ f → unjump f (¬_ ∘ isFinite) λ n → Dec¬ (decIsFinite (f n)))

--The proof of Remark-3-4 can be found after Theorem-4-4.
Remark-3-4 : (P : Type ℓ) → isProp P
           → (         P ↔ ordinal-dec (ω · ι 0) P)
           × (     Dec P ↔ ordinal-dec (ω · ι 1) P)
           × (semi-dec P ↔ ordinal-dec (ω · ι 2) P)

-- Section 4. Reduction to Limit Ordinals

Lemma-4-1 : (P : Type ℓ) (α : Brw)
          → ordinal-dec (α + ι 1) P ↔ ordinal-dec (α + ι 2) P
Lemma-4-1 P α = ordinal-dec-equivalent-finite-successors P 1

Corollary-4-2 : (P : Type ℓ) (α : Brw) (n : ℕ)
              → ordinal-dec (α + ι 1) P ↔ ordinal-dec (α + ι n + ι 1) P
Corollary-4-2 P α = ordinal-dec-equivalent-finite-successors P

-- We cannot formulate the above with just α instead α + ι 1, as can be seen by
-- taking α = ω and considering the below.
Remark-4-3 : (P : Type ℓ) → isProp P
           → (Dec P ↔ ordinal-dec ω P)
           × (semi-dec P ↔ ordinal-dec (ω + ι 1) P)
Remark-4-3 P Pprop = dec↔ω-dec P Pprop , snd (Proposition-3-2 P Pprop)

Theorem-4-4 : (β : Brw) (P : Type ℓ) → isProp P
            → ordinal-dec β P ↔ ordinal-dec (⇑ β) P
Theorem-4-4 β P Pprop = ordinal-dec-equivalent-lim-benchmark P Pprop β

NB₁ : (P : Type ℓ) → ordinal-dec (ω · ι 2) P ↔ ordinal-dec (ω + ω) P
NB₁ P = subst (λ - → ordinal-dec - P) (sym ω+ω≡ω·2) ,
        subst (λ - → ordinal-dec - P) (ω+ω≡ω·2)

NB₂ : (P : Type ℓ) → isProp P
    → ordinal-dec (ω + ι 1) P ↔ ordinal-dec (ω · ι 2) P
NB₂ P Pprop = ↔-trans (Theorem-4-4 (ω + ι 1) P Pprop) (↔-sym (NB₁ P))

Remark-3-4 P Pprop =
 ↔-sym (zero-decidable-iff-true P Pprop) ,
 ↔-trans (fst (Proposition-3-2 P Pprop)) (Theorem-4-4 one P Pprop) ,
 ((λ P-semi-dec → rl (NB₁ P) (semidec→ω·2dec P Pprop P-semi-dec)) ,
  (λ P-ord-dec → ω·2dec→semidec P Pprop (lr (NB₁ P) P-ord-dec)))

Definition-4-5 : Type ℓ → Brwᶻˡ → Type ℓ
Definition-4-5 P (ƛ , _) = ∃[ (y , _) ∈ Brwᶻˡ ] (P ↔ ƛ ≤ y)

_limit-decidable_ : Brwᶻˡ → Type ℓ → Type ℓ
ƛ limit-decidable P = Definition-4-5 P ƛ

Theorem-4-6 : (P : Type ℓ) (β : Brw) → isProp P
            → ordinal-dec β P ↔ (⇑ᶻˡ β) limit-decidable P
Theorem-4-6 P β Pprop = ↔-trans (Theorem-4-4 β P Pprop) h
 where
  h' : (y : Brw) → ⇑ β ≤ y ↔ ⇑ β ≤ ⇓ y
  h' y = Lemma-2-4.[2] (⇑ β) (snd (⇑ᶻˡ β)) y
  h : ordinal-dec (⇑ β) P ↔ (⇑ᶻˡ β limit-decidable P)
  h = ∥-∥map (λ (y , l) → (⇓ᶻˡ y , ↔-trans l (h' y))) ,
      ∥-∥map (λ ((y , _) , l) → (y , l))

-- Section 5. Closure under Binary Conjunctions

-- This definition is part of Brw-Min (see Proposition 5-2).
Definition-5-1 : Brw → Brw → Brw → Type
Definition-5-1 μ α β = (γ : Brw) → (γ ≤ α) × (γ ≤ β) ↔ γ ≤ μ

Proposition-5-2 : ((x y : Brw) → Brw-Min x y) → LPO
Proposition-5-2 = Brw-Min→LPO

Theorem-5-3 : Brw → Brw → Brw
Theorem-5-3 = limMin

Theorem-5-3-ad₁ : (α β : Brw) → Brw-zero-or-limit (limMin α β)
Theorem-5-3-ad₁ = limMin-is-zl

Theorem-5-3-ad₂ : ((α , _) (β , _) : Brwᶻˡ)(γ : Brw)
                → (γ ≤ α) × (γ ≤ β) ↔ γ ≤ limMin α β
Theorem-5-3-ad₂ (α , α-zl) (β , β-zl) γ =
 (λ (u , v) → rl (⇑-left-≤ (limMin α β) (limMin-is-zl α β) γ)
                 (τ (⇑-Islim⊎zero γ) u v)) ,
 (λ w → (≤-trans w (limMin-left α β)) , (≤-trans w (limMin-right α β)))
 where
  τ : Brw-zero-or-limit (⇑ γ) → γ ≤ α → γ ≤ β → ⇑ γ ≤ limMin α β
  τ (inl γ-lim) u v = limMin-key-property (⇑ γ) γ-lim α β u' v'
   where
    u' : ⇑ γ ≤ α
    u' = subst (⇑ γ ≤_) (islim→⇑≡id α α-zl) (⇑-monotone γ α u)
    v' : ⇑ γ ≤ β
    v' = subst (⇑ γ ≤_) (islim→⇑≡id β β-zl) (⇑-monotone γ β v)
  τ (inr γ-zero) _ _ = subst (_≤ limMin α β) (sym γ-zero) ≤-zero


Lemma-5-4 : {x₁ x₂ y₁ y₂ : Brw} → x₁ ≤ x₂ → y₁ ≤ y₂ → limMin x₁ y₁ ≤ limMin x₂ y₂
Lemma-5-4 = limMin-mono

Lemma-5-5 : (x y : Brw)
          → (limMin x y ≤ x)
          × (limMin x y ≤ y)
          × (limMin x x ≡ ⇓ x)
Lemma-5-5 x y = limMin-left x y , limMin-right x y , limMin-diagonal-is-⇓ x

Theorem-5-6 : (α : Brw) (P Q : Type ℓ) → isProp P → isProp Q
            → ordinal-dec α P
            → ordinal-dec α Q
            → ordinal-dec α (P × Q)
Theorem-5-6 α P Q i j = ordinal-dec-× P Q i j α

-- Section 6. Small Closures under Binary Disjunctions

-- This definition is part of Brw-Max (see Proposition 6-2).
Definition-6-1 : Brw → Brw → Brw → Type
Definition-6-1 ν α β = (γ : Brw) → (γ ≤ α) ⊎ (γ ≤ β) ↔ γ ≤ ν

Proposition-6-2 : ((x y : Brwᶻˡ) → Brwᶻˡ-Max x y) → LPO
Proposition-6-2 = Brwᶻˡ-Max→LPO

Theorem-6-3 : Brwᶻˡ → Brwᶻˡ → Brwᶻˡ
Theorem-6-3 = limMaxᶻˡ

Theorem-6-3-ad : (x y : Brw) (k : ℕ) → let α = ω · ι k in
                 ∥ ((α ≤ x) ⊎ (α ≤ y)) ∥ ↔ α ≤ limMax x y
Theorem-6-3-ad x y k = [1] , [2]
 where
  [1] : ∥ (ω · ι k ≤ x) ⊎ (ω · ι k ≤ y) ∥ → ω · ι k ≤ limMax x y
  [1] = ∥-∥rec ≤-trunc ([1]' k)
   where
    [1]' : (k : ℕ) → (ω · ι k ≤ x) ⊎ (ω · ι k ≤ y) → ω · ι k ≤ limMax x y
    [1]' ℕ.zero l = ≤-zero
    [1]' (ℕ.suc k) (inl l) = limMax-left  x {y} (λ n → ω · ι k + ι n) l
    [1]' (ℕ.suc k) (inr l) = limMax-right y {x} (λ n → ω · ι k + ι n) l
  [2] : ω · ι k ≤ limMax x y → ∥ (ω · ι k ≤ x) ⊎ (ω · ι k ≤ y) ∥
  [2] = ω·k-≤-⊎-closure k x y

Theorem-6-4 : (k n : ℕ) (P Q : Type ℓ) → isProp P → isProp Q
            → ordinal-dec (ω · ι k + ι n) P
            → ordinal-dec (ω · ι k + ι n) Q
            → ordinal-dec (ω · ι k + ι n) ∥ P ⊎ Q ∥
Theorem-6-4 = ordinal-dec-∨

-- Section 7.  Semidecidable Families and Quantifiers

-- The paper uses the following notation:
Ψ : (P : ℕ → Type ℓ) → ((n : ℕ) → semi-dec (P n)) → Brw
Ψ = characteristic-ordinal

Ψ＿ : (n : ℕ) → (P : ℕ → Type ℓ) → P semi-dec-up-to n → Brw
Ψ＿ n P = P characteristic-ordinal-up-to n

Ψ⁺＿ : (n : ℕ) → (P : ℕ → Type ℓ) → P semi-dec-str-up-to n → Brw
Ψ⁺＿ n P = semi-dec-limit-ordinal P n
 where
  open CharacteristicOrdinal.CharacteristicOrdinal-Construction₂

Ψ̅＿ : (n : ℕ) → (P : ℕ → Type ℓ) → ((n : ℕ) → semi-dec (P n))→ Brw
Ψ̅＿ n P σ = Ψ＿ n P (semi-dec-restrict-to n σ)

Lemma-7-1 : (P : Type ℓ)
          → ((s , q) (s' , q') : semi-dec-str P)
          → ((k : ℕ) → ∃[ m ∈ ℕ ] s  k B.≤ s' m)
          × ((k : ℕ) → ∃[ m ∈ ℕ ] s' k B.≤ s  m)
Lemma-7-1 P 𝕤 𝕤' = semi-dec-sim P 𝕤 𝕤' , semi-dec-sim P 𝕤' 𝕤

Lemma-7-2 : (P : ℕ → Type ℓ) → (n : ℕ) → Weakly-Constant (Ψ⁺＿ n P)
Lemma-7-2 = CharacteristicOrdinal.semi-dec-limit-ordinal-weakly-constant

Definition-7-3 : (P : ℕ → Type ℓ) → ((n : ℕ) → semi-dec (P n)) → Brw
Definition-7-3 = Ψ

Lemma-7-4-1 : (P : ℕ → hProp ℓ)
            → (α : Brw)
            → ((i : ℕ) → ordinal-dec α ⟨ P i ⟩)
            → Σ[ Q ∈ (ℕ → hProp ℓ) ]
                 ((i : ℕ) → ordinal-dec α ⟨ Q i ⟩) ×
                 ((i : ℕ) → ⟨ Q (suc i) ⟩ → ⟨ Q i ⟩) ×
                 ((∀ k → ⟨ P k ⟩) ↔ (∀ k → ⟨ Q k ⟩))
Lemma-7-4-1 {ℓ} P α α-dec =
 Q , Q-ord-dec , T-down-closed , ↔-sym T-equivalent-∀
  where
   open down-closed (⟨_⟩ ∘ P)
   Q : ℕ → hProp ℓ
   Q n = T n , T-is-prop (str ∘ P) n
   Q-ord-dec : (i : ℕ) → ordinal-dec α ⟨ Q i ⟩
   Q-ord-dec = T-ord-dec α (str ∘ P) α-dec

Lemma-7-4-2 : (P : ℕ → hProp ℓ)
            → (k n : ℕ)
            → ((i : ℕ) → ordinal-dec (ω · ι k + ι n) (⟨ P i ⟩))
            → Σ[ Q ∈ (ℕ → hProp ℓ) ]
                 ((i : ℕ) → ordinal-dec (ω · ι k + ι n) (⟨ Q i ⟩)) ×
                 ((i : ℕ) → ⟨ Q i ⟩ → ⟨ Q (suc i) ⟩) ×
                 (∥ Σ[ k ∈ ℕ ] ⟨ P k ⟩ ∥ ↔ ∥ Σ[ k ∈ ℕ ] ⟨ Q k ⟩ ∥)
Lemma-7-4-2 {ℓ} P k n ωk+n-dec =
 Q , Q-ord-dec , T-up-closed , ↔-sym T-equivalent-∃
  where
   open up-closed (⟨_⟩ ∘ P)
   Q : ℕ → hProp ℓ
   Q n = T n , T-is-prop (str ∘ P) n

   Q-ord-dec : (i : ℕ) → ordinal-dec (ω · ι k + ι n) (⟨ Q i ⟩)
   Q-ord-dec = T-ord-dec k n (str ∘ P) ωk+n-dec

Theorem-7-5 : (P : ℕ → hProp ℓ)
            → ((n : ℕ) → semi-dec ⟨ P n ⟩)
            → ordinal-dec (ω · ω) (∀ n → ⟨ P n ⟩)
Theorem-7-5 P P-semi-dec = ∣ Pₙ-ωdec→∀nPₙ-ω²dec (⟨_⟩ ∘ P) (str ∘ P) P-semi-dec ∣

Lemma-7-6 : (P : ℕ → Type ℓ)
          → (σ : (n : ℕ) → semi-dec (P n))
          → ∥ Σ[ n ∈ ℕ ] ω · ι 2 ≤ Ψ̅＿ n P σ ∥
          ↔ ∥ Σ[ m ∈ ℕ ] P m ∥
Lemma-7-6 P σ = characteristic-ordinal-up-to-spec' P σ

Lemma-7-7 : (P : ℕ → Type ℓ)
          → (σ : (n : ℕ) → semi-dec (P n))
          → (k : ℕ)
          → ω · ω ≤ Ψ P σ
          → ω · ω ≤ Ψ (λ i → P (k N+ i)) (λ i → σ (k N+ i))
Lemma-7-7 = cut-preserves-characteristic-ordinal-≥ω²

Lemma-7-8 : (P : ℕ → Type ℓ)
          → (σ : (n : ℕ) → semi-dec (P n))
          → down-closed P
          → (n : ℕ)
          → P n
          → Ψ̅＿ n P σ ≡ ω · ι (suc n)
Lemma-7-8 P σ P-down-closed n p =
 ≤-antisym (characteristic-ordinal-up-to-bounded P σ n) [1]
  where
   [1] : ω · ι (suc n) ≤ Ψ̅＿ n P σ
   [1] = limit-reach-next-ω' (Ψ̅＿ n P σ)
           (characteristic-ordinal-up-to-is-lim P σ n)
           n
           (characteristic-ordinal-up-to-above-ωn P σ P-down-closed n p)

Corollary-7-9-1 : (P : ℕ → hProp ℓ)
                → ((n : ℕ) → Dec ⟨ P n ⟩)
                → ordinal-dec (ω · ω) (∀ n → ⟨ P n ⟩)
Corollary-7-9-1 P P-dec =
 Theorem-7-5 P (λ n → ∣ dec→semi-dec ⟨ P n ⟩ (P-dec n) ∣)

Corollary-7-9-2 : (P : Type ℓ)
                → semi-dec P
                → ordinal-dec (ω · ω) (¬ P)
Corollary-7-9-2 P = ∥-∥rec isPropPropTrunc [1]
 where
  [1] : semi-dec-str P → ordinal-dec (ω · ω) (¬ P)
  [1] (s , w) = lr (ordinal-dec-stable-under-↔ _ _ (↔-sym [2])) [3]
   where
    [2] : ¬ P ↔ ∀ n → s n ≡ B.false
    [2] = [2]₁ , [2]₂
     where
      [2]₁ : ¬ P → (n : ℕ) → s n ≡ B.false
      [2]₁ ν n = B.¬true→false (s n) (λ e → ν (rl w ∣ n , e ∣))
      [2]₂ : ((n : ℕ) → s n ≡ B.false) → ¬ P
      [2]₂ h p = ∥-∥rec isProp⊥
                        (λ (n , e) → B.false≢true (sym (h n) ∙ e)) (lr w p)
    [3] : ordinal-dec (ω · ω) (∀ n → s n ≡ B.false)
    [3] = Corollary-7-9-1 (λ n → ((s n ≡ B.false) , B.isSetBool (s n) B.false))
                          (λ n → (s n) B.≟ B.false)

Theorem-7-10 : (P : ℕ → hProp ℓ)
             → ((n : ℕ) → semi-dec ⟨ P n ⟩)
             → ordinal-dec (ω · ι 3) (∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥)
Theorem-7-10 P σ = ∣ Pₙ-ωdec→∃nPₙ-ω·3dec' (⟨_⟩ ∘ P) (str ∘ P) σ ∣

Lemma-7-11 : (P Q : ℕ → Type ℓ)
             (σ : (n : ℕ) → semi-dec (P n))
             (τ : (n : ℕ) → semi-dec (Q n))
           → ((n : ℕ) → P n → Q n)
           → Ψ P σ ≤ Ψ Q τ
Lemma-7-11 P Q σ τ h = characteristic-ordinal-mono P Q h σ τ

Theorem-7-12 : (P : ℕ → ℕ → Type ℓ)
             → ((n m : ℕ) → isProp (P n m))
             → ((n m : ℕ) → semi-dec (P n m))
             → ((n : ℕ) → up-closed (P n))
             → ordinal-dec (ω · ω + ω) (∃[ m ∈ ℕ ] ∀ n → P n m)
Theorem-7-12 P i s u = ∣ ∃∀Semidec P i s u ∣

-- Section 8. Ordinal Decidability and Countable Choice

Lemma-8-1 : CountableChoice ℓ → Semidecidable-Closed-Under-Countable-Joins ℓ
Lemma-8-1 = CC-implies-semidec-closed-under-countable-joins

Lemma-8-2 : (α β : Brw)
          → ((x : Brw) → ordinal-dec β (α ≤ x))
          → (P : Type ℓ)
          → ordinal-dec α P → ordinal-dec β P
Lemma-8-2 α β hyp P = ∥-∥rec isPropPropTrunc τ
 where
  τ : ordinal-dec-str α P → ordinal-dec β P
  τ (x , σ) = rl (ordinal-dec-stable-under-↔ P (α ≤ x) σ) (hyp x)

Theorem-8-3 : CountableChoice ℓ-zero
            → (P : Type ℓ)
            → isProp P
            → (k : ℕ)
            → ordinal-dec (ω · ι k) P
            → semi-dec P
Theorem-8-3 = CC-implies-ω·n-dec-is-semi-dec

Theorem-8-4
 : (∀ {ℓ} (P : Type ℓ) → isProp P → ordinal-dec (ω · ω) P → semi-dec P)
 → MP → LPO
Theorem-8-4 hyp mp = MP-and-ω²-collapse-imply-LPO mp hyp

Theorem-8-5  : CountableChoice ℓ-zero
             → (P : Type ℓ)
             → isProp P
             → ordinal-dec (ω · ω) P
             → ∃[ Q ∈ (ℕ → hProp ℓ-zero) ]
                 (((n : ℕ) → semi-dec ⟨ Q n ⟩) × ((∀ n → ⟨ Q n ⟩) ↔ P))
Theorem-8-5 cc P P-prop σ =
 ∥-∥map τ (CC-implies-ω²-decidable-are-∀-of-semidecidable-props cc P P-prop σ)
 where
  τ : Σ[ Q ∈ (ℕ → Type) ] ((n : ℕ) → isProp (Q n)) × _
    → Σ[ Q ∈ (ℕ → hProp ℓ-zero) ] _
  τ (Q , Q-prop , σ , ξ) = (λ n → Q n , Q-prop n) , σ , ξ

Theorem-8-6 : CountableChoice (ℓ-max (ℓ-suc ℓ-zero) ℓ)
            → (P : ℕ → hProp ℓ)
            → (( n : ℕ ) → ordinal-dec (ω · ω) ⟨ P n ⟩)
            → ordinal-dec (ω · ω) (∀ n → ⟨ P n ⟩)
Theorem-8-6 cc P = CC-implies-ω²-dec-closed-under-∀ cc (⟨_⟩ ∘ P) (str ∘ P)

Definition-8-7 : Type ℓ-zero
Definition-8-7 = 𝕊

Definition-8-8 : Type ℓ → Type ℓ
Definition-8-8 = 𝕊-dec

Lemma-8-9 : CountableChoice ℓ-zero
          → (P : Type ℓ)
          → isProp P
          → semi-dec P ↔ 𝕊-dec P
Lemma-8-9 = CC-implies-semidec-and-𝕊-dec-coincide

Lemma-8-10 : (P : Type ℓ) → Dec P → 𝕊-dec P
Lemma-8-10 P = Dec→𝕊-dec

Proposition-8-11 : (P : Type ℓ)
                 → isProp P
                 → (n k : ℕ)
                 → ordinal-dec (ω · ι n + ι k) P
                 → 𝕊-dec P
Proposition-8-11 P P-prop n k = ∥-∥rec (isProp𝕊Dec P-prop) τ
 where
  τ : ordinal-dec-str (ω · ι n + ι k) P → 𝕊-dec P
  τ (x , σ) = rl (𝕊-dec-stable-under-↔ σ) (below-ω²-sdec x n k)

-- Section 9. On the Agda Formalization

relational-approach : Brw → Brw → Brw → Type
relational-approach = limMin[_,_]~_

Equation-9 : {x x' y y' z z' : Brw}
           → x ≤ x' → y ≤ y'
           → limMin[ x , y ]~ z → limMin[ x' , y' ]~ z' → z ≤ z'
Equation-9 = limMin[,]~-mono

NB : (f : ℕ → Brw) (y : Brw) {f↑ : increasing f}
   → limMin (limit f {f↑}) (succ y) ≡ limMin (limit f {f↑}) y
NB f y = refl

meta-lemma : _
meta-lemma = characteristic-ordinal-up-to-reduction-lemma

meta-lemma' : _
meta-lemma' = characteristic-ordinal-up-to-reduction-lemma₂