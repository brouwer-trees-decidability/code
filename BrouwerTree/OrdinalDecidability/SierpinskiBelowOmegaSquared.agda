{-# OPTIONS --cubical --guardedness --erasure #-}
module BrouwerTree.OrdinalDecidability.SierpinskiBelowOmegaSquared where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty as ⊥ using (rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc; predℕ; _≡ᵇ_; ≡ᵇ→≡)
                             renaming (_+_ to _N+_)
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Bool
 using (Bool; true; false; isSetBool; false≢true; _≟_; Bool→Type)
open import Cubical.Relation.Nullary.Base using (Dec; yes; no)

open import General-Properties
open import Iff
open import PropTrunc

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Code.Results
open import BrouwerTree.Decidability.Finite
open import BrouwerTree.Arithmetic
open import BrouwerTree.Arithmetic.Properties

open import BrouwerTree.OrdinalDecidability.Basic
open import BrouwerTree.OrdinalDecidability.QuantificationTheorem
open import BrouwerTree.OrdinalDecidability.Sierpinski

private
  variable
    ℓ ℓ' : Level

-- For a cantor normal form below ω² (written as ω·n + k) and any
-- Brouwer ordinal x, it is 𝕊-decidable whether x ≥ ω·n+k.

below-ω²-sdec : (x : Brw) → (n k : ℕ) → 𝕊-dec (ω · ι n + ι k ≤ x)
below-ω²-sdec x zero k =
 dec→𝕊-dec _ (subst (λ - → Dec (- ≤ x)) (sym (zero+y≡y (ι k))) (dec-n≤ x k))
below-ω²-sdec zero (suc n) k = ⊥ , ⊥.rec ∘ [1] k , ⊥.rec ∘ ⊥≠⊤
 where
  [1] : (k : ℕ) → (a : (limit (λ m → ω · ι n + ι m) + ι k) ≤ zero) → ⊥.⊥
  [1] zero = lim≰zero
  [1] (suc k) = succ≰zero
below-ω²-sdec (succ x) (suc n) zero =
 ⌊ below-ω²-sdec x (suc n) zero ⌋ ,
 (ω · ι (suc n) ≤ succ x
   ↔⟨ lim≤sx↔lim≤x (λ k → ω · ι n + ι k) x ⟩
  ω · ι (suc n) ≤ x
   ↔⟨ ⌊ below-ω²-sdec x (suc n) zero ⌋-correct ⟩
  ⌊ below-ω²-sdec x (suc n) zero ⌋ ≡ ⊤ ↔∎)
below-ω²-sdec (succ x) (suc n) (suc k) =
 ⌊ below-ω²-sdec x (suc n) k ⌋ ,
 ((succ (ω · ι (suc n) + ι k) ≤ succ x)
   ↔⟨ ≤-succ-mono-↔ ⟩
  ((ω · ι (suc n) + ι k) ≤ x)
   ↔⟨ ⌊ below-ω²-sdec x (suc n) k ⌋-correct ⟩
  ⌊ below-ω²-sdec x (suc n) k ⌋ ≡ ⊤ ↔∎)
below-ω²-sdec x@(limit f {f↑}) (suc n) zero = γ
 module M₀ where
  γ = ⋁ (λ k → ⌊ below-ω²-sdec (f k) n 0 ⌋) ,
      (ω · ι (suc n) ≤ limit f
        ↔⟨ lim≤lim↔weakly-bisimilar (λ k → ω · ι n + ι k) f ⟩
       ((m : ℕ) → ∃[ k ∈ ℕ ] ω · ι n + ι m ≤ f k)
        ↔⟨ [1] , [2] ⟩
       ∃[ k ∈ ℕ ] ω · ι n ≤ f k
        ↔⟨ ∥-∥↔ (map-snd (λ {k} → lr ⌊ below-ω²-sdec (f k) n 0 ⌋-correct) ,
                 map-snd (λ {k} → rl ⌊ below-ω²-sdec (f k) n 0 ⌋-correct)) ⟩
       ∃[ k ∈ ℕ ] ⌊ below-ω²-sdec (f k) n 0 ⌋ ≡ ⊤
        ↔⟨ ↔-sym (is-⊤↔contains-⊤ (λ k → ⌊ below-ω²-sdec (f k) n 0 ⌋)) ⟩
       ⋁ (λ k → ⌊ below-ω²-sdec (f k) n 0 ⌋) ≡ ⊤ ↔∎)
       where
        [1] : ((m : ℕ) → ∃[ k ∈ ℕ ] ω · ι n + ι m ≤ f k)
            → ∃[ k ∈ ℕ ] ω · ι n ≤ f k
        [1] p = p 0
        [2] : ∃[ k ∈ ℕ ] ω · ι n ≤ f k → (m : ℕ) → ∃[ k ∈ ℕ ] ω · ι n + ι m ≤ f k
        [2] p m = ∥-∥map (λ (k , l) → (k N+ m) , ≤-offset-by-ι f {f↑} (ω · ι n) {k} {m} l) p
below-ω²-sdec x@(limit f) (suc n) (suc zero) = δ
 module M₁ where
  δ = ⋁ (λ k → ⌊ below-ω²-sdec (f k) (suc n) 1 ⌋) ,
      (ω · ι (suc n) < limit f
        ↔⟨ below-limit-↔ (ω · ι (suc n)) f ⟩
       ∃[ k ∈ ℕ ] (ω · ι (suc n)) < f k
        ↔⟨ ∥-∥↔ [1] ⟩
       ∃[ k ∈ ℕ ] ⌊ below-ω²-sdec (f k) (suc n) 1 ⌋ ≡ ⊤
        ↔⟨ ↔-sym (is-⊤↔contains-⊤ (λ k → ⌊ below-ω²-sdec (f k) (suc n) 1 ⌋)) ⟩
       ⋁ (λ k → ⌊ below-ω²-sdec (f k) (suc n) 1 ⌋) ≡ ⊤ ↔∎)
       where
        [1] : (Σ[ k ∈ ℕ ] (ω · ι (suc n)) < f k)
            ↔ (Σ[ k ∈ ℕ ] ⌊ below-ω²-sdec (f k) (suc n) 1 ⌋ ≡ ⊤)
        [1] = map-snd (λ {k} → lr (⌊ below-ω²-sdec (f k) (suc n) 1 ⌋-correct)) ,
              map-snd (λ {k} → rl (⌊ below-ω²-sdec (f k) (suc n) 1 ⌋-correct))
below-ω²-sdec x@(limit f) (suc n) (suc (suc k)) =
 ⌊ below-ω²-sdec x (suc n) (suc k) ⌋ ,
 (ω · ι (suc n) + ι (suc k) < limit f
   ↔⟨ ↔-sym (x<lim↔sx<lim f (ω · ι (suc n) + ι k)) ⟩
  ω · ι (suc n) + ι (suc k) ≤ limit f
   ↔⟨ ⌊ below-ω²-sdec (limit f) (suc n) (suc k) ⌋-correct ⟩
  ⌊ below-ω²-sdec (limit f) (suc n) (suc k) ⌋ ≡ ⊤ ↔∎)
-- All coherences are automatic, since `𝕊-dec ...` is a proposition
below-ω²-sdec (bisim f g x i) (suc n) 0 =
  isProp→PathP {B = λ i → 𝕊-dec (ω · (ι (suc n)) ≤ bisim f g x i)}
               (λ i → isProp𝕊Dec isProp⟨≤⟩) (M₀.γ f n) (M₀.γ g n) i
below-ω²-sdec (bisim f g x i) (suc n) 1 =
 isProp→PathP {B = λ i → 𝕊-dec (ω · (ι (suc n)) + ι 1 ≤ bisim f g x i)}
              (λ i → isProp𝕊Dec isProp⟨≤⟩) (M₁.δ f n) (M₁.δ g n) i
below-ω²-sdec (bisim f g x i) (suc n) (suc (suc k)) =
  let δ = (⌊ below-ω²-sdec (limit f) (suc n) (suc k) ⌋ ,
          ((succ (limit (λ n₁ → ω · ι n + ι n₁) + ι k) < limit f) ↔⟨
           ↔-sym (x<lim↔sx<lim f (limit (λ n₁ → ω · ι n + ι n₁) + ι k)) ⟩
           (succ (limit (λ n₁ → ω · ι n + ι n₁) + ι k) ≤ limit f) ↔⟨
           ⌊ below-ω²-sdec (limit f) (suc n) (suc k) ⌋-correct ⟩
           ⌊ below-ω²-sdec (limit f) (suc n) (suc k) ⌋ ≡ ⊤ ↔∎))
      γ = (⌊ below-ω²-sdec (limit g) (suc n) (suc k) ⌋ ,
          ((succ (limit (λ n₁ → ω · ι n + ι n₁) + ι k) < limit g) ↔⟨
           ↔-sym (x<lim↔sx<lim g (limit (λ n₁ → ω · ι n + ι n₁) + ι k)) ⟩
           (succ (limit (λ n₁ → ω · ι n + ι n₁) + ι k) ≤ limit g) ↔⟨
           ⌊ below-ω²-sdec (limit g) (suc n) (suc k) ⌋-correct ⟩
           ⌊ below-ω²-sdec (limit g) (suc n) (suc k) ⌋ ≡ ⊤ ↔∎)) in
  isProp→PathP
   {B = λ i → 𝕊-dec (ω · (ι (suc n)) + ι (suc (suc k)) ≤ bisim f g x i)}
   (λ i → isProp𝕊Dec isProp⟨≤⟩) δ γ i
below-ω²-sdec (trunc x y p q i j) (suc n) k =
 isProp→SquareP' {B = λ i j → 𝕊-dec ((ω · ι (suc n) + ι k) ≤ trunc x y p q i j)}
                 (λ i j → isProp𝕊Dec isProp⟨≤⟩)
                 (λ j → below-ω²-sdec x (suc n) k)
                 (λ j → below-ω²-sdec y (suc n) k)
                 (λ j → below-ω²-sdec (p j) (suc n) k)
                 (λ j → below-ω²-sdec (q j) (suc n) k) i j

below-ω²-sdec-witness-succ
 : (n k : ℕ) (x : Brw)
 → ⌊ below-ω²-sdec (succ x) (suc n) k ⌋ ≡ ⌊ below-ω²-sdec x (suc n) (predℕ k) ⌋
below-ω²-sdec-witness-succ n zero x = refl
below-ω²-sdec-witness-succ n (suc k) x = refl

below-ω²-sdec-witness-limit
 : (n k : ℕ) (f : ℕ → Brw) {f↑ : increasing f}
 → ⌊ below-ω²-sdec (limit f {f↑}) (suc n)  (suc k) ⌋ ≡ ⌊ below-ω²-sdec (limit f {f↑}) (suc n) 1 ⌋
below-ω²-sdec-witness-limit n zero f = refl
below-ω²-sdec-witness-limit n (suc k) f = below-ω²-sdec-witness-limit n k f

{-
  As shown by Escardó and Knapp [1], and formalized by Tom de Jong in [2], the
  following are equivalent:
  - the semidecidable propositions are closed under Σ,
  - the semidecidable propositions form a dominance,
  - a weak choice principle, dubbed* Escardo-Knapp-Choice in [2] and recalled
    below.

  * This should not be confused with a related principle also called
    Escardó-Knapp Choice (EKC) as introduced by Andrew Swan in two talks from
    2019. Swan's choice principle is stronger than the one considered here.
    - https://logic.math.su.se/mloc-2019/slides/Swan-mloc-2019-slides.pdf
    - https://www.math.uwo.ca/faculty/kapulkin/seminars/hottestfiles/Swan-2019-11-06-HoTTEST.pdf

  [1] Martín H. Escardó and Cory M. Knapp.
      ‘Partial Elements and Recursion via Dominances in Univalent Type Theory’.
      In: 26th EACSL Annual Conference on Computer Science Logic (CSL 2017).
      Ed. by Valentin Goranko and Mads Dam. Vol. 82. Leibniz International
      Proceedings in Informatics (LIPIcs).
      Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2017, 21:1–21:16.
      doi: 10.4230/LIPIcs.CSL.2017.21
  [2] Tom de Jong
      January 2022
      Agda file with comments
      https://cs.bham.ac.uk/~mhe/TypeTopology/NotionsOfDecidability.SemiDecidable.html
-}

Escardo-Knapp-Choice : (ℓ ℓ' : Level) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Escardo-Knapp-Choice ℓ ℓ' = (P : Type ℓ) (Q : Type ℓ')
                          → isProp P → (P → isProp Q)
                          → semi-dec P → (P → semi-dec Q)
                          → ∥ (P → semi-dec-str Q) ∥

Semidecidable-Closed-Under-Σ : (ℓ ℓ' : Level) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Semidecidable-Closed-Under-Σ ℓ ℓ' = (P : Type ℓ)
                                  → isProp P
                                  → semi-dec P
                                  → (Q : P → Type ℓ')
                                  → ((p : P) → isProp (Q p))
                                  → ((p : P) → semi-dec (Q p))
                                  → semi-dec (Σ P Q)

Semidecidable-Closed-Under-Countable-Joins : (ℓ : Level) → Type (ℓ-suc ℓ)
Semidecidable-Closed-Under-Countable-Joins ℓ = (P : ℕ → Type ℓ)
                                             → ((n : ℕ) → isProp (P n))
                                             → ((n : ℕ) → semi-dec (P n))
                                             → semi-dec (∃ ℕ P)


semidecidable-closed-under-Σ-implies-EKC : Semidecidable-Closed-Under-Σ ℓ ℓ'
                                         → Escardo-Knapp-Choice ℓ ℓ'
semidecidable-closed-under-Σ-implies-EKC H P Q P-prop Q-prop ρ σ = ∥-∥map g τ
 where
  τ : semi-dec (P × Q)
  τ = H P P-prop ρ (λ _ → Q) Q-prop σ

  g : semi-dec-str (P × Q) → P → semi-dec-str Q
  g ss p = lr (semi-dec-str-stable-under-↔ (P × Q) Q (snd , λ q → p , q)) ss

-- The below is adapted from from [2].
semidecidable-closed-under-countable-joins-implies-also-closed-under-Σ
 : Semidecidable-Closed-Under-Countable-Joins (ℓ-max ℓ ℓ')
 → Semidecidable-Closed-Under-Σ ℓ ℓ'
semidecidable-closed-under-countable-joins-implies-also-closed-under-Σ {ℓ = ℓ} {ℓ' = ℓ'} H P P-prop ρ Q Q-prop σ =
 ∥-∥rec isPropPropTrunc τ ρ
  where
   τ : semi-dec-str P → ∥ semi-dec-str (Σ P Q) ∥
   τ (α , e) = lr (semi-dec-stable-under-↔ (∃ ℕ Q̃) _ ΣQ̃-ΣQ-↔)
                  (H Q̃ Q̃-is-prop-valued Q̃-is-semidecidable)
    where
     abstract
       P̃ : ℕ → hProp ℓ
       P̃ n = Lift (α n ≡ true) , isPropLift (isSetBool _ _)

       P̃-is-decidable : (n : ℕ) → Dec (typ (P̃ n))
       P̃-is-decidable n with α n
       ... | false = no (λ e → false≢true (lower e))
       ... | true = yes (lift refl)

       P̃-property : ∃[ n ∈ ℕ ] α n ≡ true ↔ (Σ[ n ∈ ℕ ] typ (P̃ n))
       P̃-property = f , g
        where
         f : ∃[ n ∈ ℕ ] α n ≡ true → Σ[ n ∈ ℕ ] typ (P̃ n)
         f = map-snd lift ∘ least-witness _ (λ n → isSetBool _ _) (λ n → α n ≟ true)
         g : Σ[ n ∈ ℕ ] typ (P̃ n) → ∃[ n ∈ ℕ ] α n ≡ true
         g (n , lift e) = ∣ n , e ∣

       ΣP̃-to-P : (Σ[ n ∈ ℕ ] typ (P̃ n)) → P
       ΣP̃-to-P = rl e ∘ rl P̃-property

     Q̃ : ℕ → Type (ℓ-max ℓ ℓ')
     Q̃ n = Σ[ p ∈ typ (P̃ n) ] Q (ΣP̃-to-P (n , p))

     Q̃-is-prop-valued : (n : ℕ) → isProp (Q̃ n)
     Q̃-is-prop-valued n = isPropΣ (str (P̃ n)) (λ p → Q-prop (ΣP̃-to-P (n , p)))

     ΣQ̃-ΣQ-↔ : ∃ ℕ Q̃ ↔ Σ P Q
     ΣQ̃-ΣQ-↔ = ∥-∥rec (isPropΣ P-prop Q-prop)
                      (λ (n , p̃ , q) → ΣP̃-to-P (n , p̃) , q )
             , λ (p , q) → ∣ fst (lr P̃-property (lr e p)) ,
                             snd (lr P̃-property (lr e p)) ,
                             subst Q (P-prop _ _) q ∣

     Q̃-is-semidecidable : (n : ℕ) → semi-dec (Q̃ n)
     Q̃-is-semidecidable n with P̃-is-decidable n
     ... | yes p̃ = lr (semi-dec-stable-under-↔ _ _ claim) (σ p)
      where
       p : P
       p = ΣP̃-to-P (n , p̃)
       claim : Q p ↔ Q̃ n
       claim = (λ q → p̃ , q) ,
               (λ (p̃' , q) → subst (λ - → Q (ΣP̃-to-P (n , -))) (str (P̃ n) _ _) q)
     ... | no ¬p̃ = lr (semi-dec-stable-under-↔ _ _ claim)
                      ∣ dec→semi-dec _ (no (λ e → e)) ∣
      where
       claim : ⊥.⊥ ↔ Q̃ n
       claim = ⊥.rec , (λ (p̃ , q) → ¬p̃ p̃)

-- We now use the above result to separate 𝕊-decidability and
-- semidecidability.

𝕊-decidable-closed-under-countable-joins : (P : ℕ → Type ℓ)
                                         → ((n : ℕ) → 𝕊-dec (P n))
                                         → 𝕊-dec (∃ ℕ P)
𝕊-decidable-closed-under-countable-joins P ρ =
 ⋁ (λ n → ⌊ ρ n ⌋) , (∃[ n ∈ ℕ ] P n          ↔⟨ ∥-∥↔ (map-snd (lr (⌊ ρ _ ⌋-correct)) ,
                                                       map-snd (rl (⌊ ρ _ ⌋-correct))) ⟩
                      ∃[ n ∈ ℕ ]  ⌊ ρ n ⌋ ≡ ⊤ ↔⟨ ↔-sym (is-⊤↔contains-⊤ (λ n → ⌊ ρ n ⌋)) ⟩
                      ⋁ (λ n → ⌊ ρ n ⌋) ≡ ⊤       ↔∎)

𝕊-dec→Semi-dec-implies-semidecidable-closed-under-Σ
 : ((P : Type ℓ) → 𝕊-dec P → semi-dec P)
 → Semidecidable-Closed-Under-Countable-Joins ℓ
𝕊-dec→Semi-dec-implies-semidecidable-closed-under-Σ H P P-is-Prop ρ =
 H (∃ ℕ P) (𝕊-decidable-closed-under-countable-joins
             P
             (λ n → semidec→𝕊-dec (P n) (P-is-Prop n) (ρ n)))

ω3≤x-semidec-implies-semidecidable-closed-under-countable-joins
 : ((x : Brw) → semi-dec (ω · ι 3 ≤ x))
 → Semidecidable-Closed-Under-Countable-Joins ℓ
ω3≤x-semidec-implies-semidecidable-closed-under-countable-joins H P P-is-prop ρ =
 ∥-∥map (lr (semi-dec-str-stable-under-↔ _ _ (↔-sym σ))) (H x)
  where
   x = fst (Pₙ-ωdec→∃nPₙ-ω·3dec' P P-is-prop ρ)
   σ = snd (Pₙ-ωdec→∃nPₙ-ω·3dec' P P-is-prop ρ)

ω3≤x-semidec-implies-EKC : ((x : Brw) → semi-dec (ω · ι 3 ≤ x)) → Escardo-Knapp-Choice ℓ ℓ'
ω3≤x-semidec-implies-EKC =
 semidecidable-closed-under-Σ-implies-EKC ∘
 semidecidable-closed-under-countable-joins-implies-also-closed-under-Σ ∘
 ω3≤x-semidec-implies-semidecidable-closed-under-countable-joins
