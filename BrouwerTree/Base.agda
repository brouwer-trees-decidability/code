----------------------------------------------------------------------------------------------------
-- Brouwer trees as a quotient inductive-inductive type
----------------------------------------------------------------------------------------------------

{- Brouwer trees consisting of zero, succ, and limits of strictly
   increasing sequences.  The path constructor of the ordinal type
   says that bisimilar sequences give equal limits.  The type of
   Brouwer trees with this definition will not be a set automatically.
   Therefore, a truncation constructor is added. -}

{-# OPTIONS --cubical --erasure --guardedness --safe #-}

module BrouwerTree.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function

open import Cubical.Data.Nat

open import BrouwerTree.Core public

{- Simple induction principles

   We show two simple special cases of the general induction principle:
   One for propositional propertier of ordinals, and one for propositional
   properties of inequalities.
-}

{- The first one is called Brw-ind, and is defined in BrouwerTree.Core -}

{- The second principle is called ≤-ind.-}
≤-ind : ∀ {a} →
        (P : ∀ {x y} → x ≤ y → Type a) →
        (∀ {x y} x≤y → isProp (P {x} {y} x≤y)) →
        (∀ {x} → P (≤-zero {x})) →
        (∀ {x y z} {x≤y : x ≤ y} {y≤z : y ≤ z} → P x≤y → P y≤z → P (≤-trans x≤y y≤z)) →
        (∀ {x y} (x≤y : x ≤ y) → P x≤y → P (≤-succ-mono x≤y)) →
        (∀ {x} f {f↑} {k} → (x≤fk : x ≤ f k) → P (x≤fk) → P (≤-cocone {x} f {f↑} {k} x≤fk)) →
        (∀ f {f↑} {y} f≤y → (∀ k → P (f≤y k)) → (∀ k → P (f↑ k)) → P (≤-limiting f {f↑} {y} f≤y)) →
        {x y : Brw} → (x≤y : x ≤ y) → P x≤y
≤-ind P prop z t s c l {.zero} {y} ≤-zero = z
≤-ind P prop z t s c l {x} {y} (≤-trans x≤x₁ x₁≤y) =
    t (≤-ind P prop z t s c l x≤x₁) (≤-ind P prop z t s c l x₁≤y)
≤-ind P prop z t s c l {.(succ x)} {.(succ y)} (≤-succ-mono {x} {y} x≤y) =
    s x≤y (≤-ind P prop z t s c l x≤y)
≤-ind P prop z t s c l {x} {.(limit f)} (≤-cocone f {k = k} x≤fk) =
    c f {k = k} x≤fk (≤-ind P prop z t s c l x≤fk)
≤-ind P prop z t s c l {.(limit f)} {y} (≤-limiting f {f↑} {x} f≤y) =
    l f {f↑} {y} f≤y (λ k → ≤-ind P prop z t s c l (f≤y k)) (λ k → ≤-ind P prop z t s c l (f↑ k))
≤-ind P prop z t s c l {x} {y} (≤-trunc x≤y x≤y' i) =
    isProp→PathP (λ j → prop (≤-trunc x≤y x≤y' j)) (≤-ind P prop z t s c l x≤y)
                 (≤-ind P prop z t s c l x≤y') i

{- The more general induction principle into Sets and Propositions -}

module _ {ℓ ℓ' : Level} (P : Brw → Type ℓ) (Q : (x y : Brw) → x ≤ y → P x → P y → Type ℓ')
         (isSet⟨P⟩ : (x : Brw) → isSet (P x))
         (isProp⟨Q⟩ : (x y : Brw) (x≤y : x ≤ y) (px : P x) (py : P y) → isProp (Q x y x≤y px py))
         (z : P zero)
         (s : {x : Brw} → P x → P (succ x))
         (l : ∀ {f f↑} (pf : (k : ℕ) → P (f k)) →
                ((k : ℕ) → Q (succ (f k)) (f (suc k)) (f↑ k) (s (pf k)) (pf (suc k))) →
                P (limit f {f↑}))
         (bs : ∀ {f f↑ g g↑ f≈g} →
                 (pf : (k : ℕ) → P (f k)) →
                 (pf↑ : (k : ℕ) → Q (succ (f k)) (f (suc k)) (f↑ k) (s (pf k)) (pf (suc k))) →
                 (pg : (k : ℕ) → P (g k)) →
                 (pg↑ : (k : ℕ) → Q (succ (g k)) (g (suc k)) (g↑ k) (s (pg k)) (pg (suc k))) →
                 PathP (λ i → P (bisim f {f↑} g {g↑} f≈g i)) (l pf pf↑) (l pg pg↑))
         (z≤ : ∀ {y} → (py : P y) → Q zero y (≤-zero {y}) z py)
         (t≤ : ∀ {x y z} {x≤y : x ≤ y} {y≤z : y ≤ z} (px : P x) (py : P y) (pz : P z) →
                 Q x y x≤y px py → Q y z y≤z py pz → Q x z (≤-trans x≤y y≤z) px pz)
         (s≤ : ∀ {x y} (x≤y : x ≤ y) (px : P x) (py : P y) →
                 Q x y x≤y px py → Q (succ x) (succ y) (≤-succ-mono x≤y) (s px) (s py))
         (c≤ : ∀ {x} f {f↑} {k} (x≤fk : x ≤ f k)
                 (px : P x) →
                 (pf : (k : ℕ) → P (f k)) →
                 (pf↑ : (k : ℕ) → Q (succ (f k)) (f (suc k)) (f↑ k) (s (pf k)) (pf (suc k))) →
                 (qx≤fk : Q x (f k) x≤fk px (pf k)) →
                 Q x (limit f) (≤-cocone {x} f {f↑} {k} x≤fk) px (l pf pf↑))
         (l≤ : ∀ f {f↑} {y} f≤y →
                 (pf : (k : ℕ) → P (f k)) →
                 (pf↑ : (k : ℕ) → Q (succ (f k)) (f (suc k)) (f↑ k) (s (pf k)) (pf (suc k))) →
                 (py : P y) →
                 Q (limit f) y (≤-limiting f {f↑} {y} f≤y) (l pf pf↑) py)
  where

  mutual

    Brw-elim : (x : Brw) → P x
    Brw-elim zero = z
    Brw-elim (succ x) = s (Brw-elim x)
    Brw-elim (limit f {f↑}) = l (Brw-elim ∘ f) (≤-elim ∘ f↑)
    Brw-elim (bisim f {f↑} g {g↑} f≈g i) = bs (Brw-elim ∘ f) (≤-elim ∘ f↑)
                                              (Brw-elim ∘ g) (≤-elim ∘ g↑) i
    Brw-elim (trunc x y p q i j) = isSet→SquareP {A = λ i j → P (trunc x y p q i j)}
                                                 (λ i j → isSet⟨P⟩ (trunc x y p q i j))
                                                 (λ j → Brw-elim (p j))
                                                 (λ j → Brw-elim (q j))
                                                 (λ _ → Brw-elim x)
                                                 (λ _ → Brw-elim y) i j

    ≤-elim : {x y : Brw} → (x≤y : x ≤ y) → Q x y x≤y (Brw-elim x) (Brw-elim y)
    ≤-elim {.zero} {y} ≤-zero = z≤ (Brw-elim y)
    ≤-elim {x} {y} (≤-trans {y = z} x≤z z≤y) = t≤ (Brw-elim x) (Brw-elim z) (Brw-elim y)
                                                  (≤-elim x≤z) (≤-elim z≤y)
    ≤-elim {.(succ x)} {.(succ y)} (≤-succ-mono {x} {y} x≤y) = s≤ x≤y (Brw-elim x) (Brw-elim y)
                                                                  (≤-elim x≤y)
    ≤-elim {x} {.(limit f)} (≤-cocone f {f↑} x≤fk) = c≤ f x≤fk (Brw-elim x)
                                                        (Brw-elim ∘ f) (≤-elim ∘ f↑) (≤-elim x≤fk)
    ≤-elim {.(limit f)} {y} (≤-limiting f {f↑} x) = l≤ f x (Brw-elim ∘ f) (≤-elim ∘ f↑) (Brw-elim y)
    ≤-elim {x} {y} (≤-trunc p q i) =
        isProp→PathP {B = λ i → Q x y (≤-trunc p q i) (Brw-elim x) (Brw-elim y)}
                     (λ i → isProp⟨Q⟩ x y (≤-trunc p q i) (Brw-elim x) (Brw-elim y))
                     (≤-elim p) (≤-elim q) i
