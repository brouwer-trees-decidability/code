----------------------------------------------------------------------------------------------------
-- Decidability results for finiteness and finite Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Decidability.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat as N
open import Cubical.Data.Nat.Order as N hiding (_≤_; _<_; ≤-trans; <-trans)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
  using (¬_; Dec; yes; no; isPropDec; mapDec)

open import PropTrunc

open import General-Properties
open import Iff

open import BrouwerTree.Base
open import BrouwerTree.Classifiability
open import BrouwerTree.Properties
open import BrouwerTree.Code.Results

isFinite' : Brw → hProp ℓ-zero
isFinite' zero = Unit , isPropUnit
isFinite' (succ x) = isFinite' x
isFinite' (limit f) = ⊥ , isProp⊥
isFinite' (bisim f g x i) = ⊥ , isProp⊥
isFinite' (trunc x y p q i j) =
  isSet→SquareP {A = λ i j → hProp ℓ-zero}
                (λ i j → isSetHProp)
                (λ j → isFinite' (p j))
                (λ j → isFinite' (q j))
                refl
                refl
                i j

isFinite : Brw → Type
isFinite x = typ (isFinite' x)

isProp⟨isFinite⟩ : (x : Brw) → isProp (isFinite x)
isProp⟨isFinite⟩ x = str (isFinite' x)

isFinite-correct : (x : Brw) → isFinite x ↔ ∥ Σ ℕ (λ n → ι n ≡ x) ∥
isFinite-correct x = (λ fin-x → ∣ left x fin-x ∣) , ∥-∥rec (isProp⟨isFinite⟩ x) (λ (n , p) → subst isFinite p (right n)) where
  left : (x : Brw) → isFinite x → Σ ℕ (λ n → ι n ≡ x)
  left = Brw-ind (λ x → isFinite x → Σ ℕ (λ n → ι n ≡ x))
                 (λ x → isProp→ (λ { (n , p) (m , q) → Σ≡Prop (λ n → Brw-is-set _ _) (ι-injective (p ∙ sym q))}))
                 (λ _ → (0 , refl))
                 (λ ih fin-x → let (n , ιn≡x) = ih fin-x in (suc n , cong succ ιn≡x))
                 (λ ih ())

  right : (n : ℕ) → isFinite (ι n)
  right zero = tt
  right (suc n) = right n

isFinite-correct' : (x : Brw) → isFinite x ↔ Σ ℕ (λ n → ι n ≡ x)
isFinite-correct' x = ↔-trans (isFinite-correct x) h
 where
  h : ∥ Σ ℕ (λ n → ι n ≡ x) ∥ ↔ Σ ℕ (λ n → ι n ≡ x)
  h = (∥-∥rec i (idfun _)) , ∣_∣
   where
    i : isProp (Σ ℕ (λ n → ι n ≡ x))
    i (n , e) (n' , e') =
     ΣPathP (ι-injective (e ∙ sym e') ,
             isProp→PathP (λ i → Brw-is-set _ x) e e')

isFinite-correct₂ : (x : Brw) → isFinite x ↔ x < ω
isFinite-correct₂ x = (left x , right x) where
  left : (x : Brw) → isFinite x → x < ω
  left x p = ∥-∥rec isProp⟨<⟩ (λ { (n , ιn=x) → subst (_< ω) ιn=x (<-cocone-simple ι) }) (fst (isFinite-correct x) p)

  right : (x : Brw) → x < ω → isFinite x
  right = Brw-ind (λ x → x < ω → isFinite x) (λ x → isProp→ (isProp⟨isFinite⟩ x))
                  (λ _ → tt)
                  (λ {x} ih sx<ω → ih (<-trans _ _ _ <-succ-incr-simple sx<ω))
                  λ {f} {f↑} ih lf<ω → ⊥.rec (<-irreflexive _ (<∘≤-in-< lf<ω (ω-smallest f {f↑})))


notFinite→ω≤ : (x : Brw) → ¬ isFinite x → ω ≤ x
notFinite→ω≤ = Brw-ind (λ x → ¬ isFinite x → ω ≤ x) (λ x → isProp→ isProp⟨≤⟩)
  (λ p → ⊥.rec (p tt))
  (λ {x} ih p → ≤-trans (ih p) ≤-succ-incr-simple)
  λ {f} _ p → ω-smallest f

notFinite-correct-↔ : (x : Brw) → ¬ isFinite x ↔ ω ≤ x
notFinite-correct-↔ x = notFinite→ω≤ x , λ l f → <-irreflexive ω ([1] l f)
 where
  [1] : ω ≤ x → isFinite x → ω < ω
  [1] l x-finite = ≤∘<-in-< l (lr (isFinite-correct₂ x) x-finite)

decIsFinite : (x : Brw) → Dec (isFinite x)
decIsFinite = Brw-ind (λ x → Dec (isFinite x))
                      (λ x → isPropDec (isProp⟨isFinite⟩ x))
                      (yes tt)
                      (λ ih → ih)
                      λ ih → no λ ()

<ω-or-≥ω : (x : Brw) → (x < ω) ⊎ (ω ≤ x)
<ω-or-≥ω x with decIsFinite x
... | yes p = inl (fst (isFinite-correct₂ x) p)
... | no ¬p = inr (notFinite→ω≤ x ¬p)

dec-n≡ : (x : Brw) → (n : ℕ) → Dec (ι n ≡ x)
dec-n≡ = Brw-ind (λ x → ∀ n → Dec (ι n ≡ x))
                 (λ x → isPropΠ (λ n → isPropDec (Brw-is-set _ _)))
                 (λ n → mapDec (cong ι) (λ p q → p (ι-injective q)) (discreteℕ n 0))
                 succCase
                 (λ ih n → no λ p → <-irreflexive-≡ p (ι n <lim))
  where
  succCase : {x : Brw} → ((n : ℕ) → Dec (ι n ≡ x)) → (n : ℕ) → Dec (ι n ≡ succ x)
  succCase ih zero = no zero≠succ
  succCase ih (suc n) = mapDec (cong succ) (λ p q → p (succ-injective q)) (ih n)

dec-≡n : (x : Brw) → (n : ℕ) → Dec (x ≡ ι n)
dec-≡n x n with dec-n≡ x n
... | yes n≡x = yes (sym n≡x)
... | no ¬n≡x = no (¬n≡x ∘ sym)

dec-n≤ : (x : Brw) → (n : ℕ) → Dec (ι n ≤ x)
dec-n≤ = Brw-ind (λ x → ∀ n → Dec (ι n ≤ x))
                 (λ x → isPropΠ (λ n → isPropDec (isProp⟨≤⟩)))
                 (λ n → mapDec ι-mono (λ p q → p (ι-reflecting q)) (≤Dec n 0))
                 succCase
                 λ {f} {f↑} _ n → yes (≤-cocone f (ι-pointwise-smaller f f↑ n))
  where
  succCase : {x : Brw} → ((n : ℕ) → Dec (ι n ≤ x)) → (n : ℕ) → Dec (ι n ≤ succ x)
  succCase ih zero = yes ≤-zero
  succCase ih (suc n) = mapDec ≤-succ-mono (λ p q → p (≤-succ-mono⁻¹ q)) (ih n)

dec-≤n : (x : Brw) → (n : ℕ) → Dec (x ≤ ι n)
dec-≤n = Brw-ind (λ x → ∀ n → Dec (x ≤ ι n))
                 (λ x → isPropΠ (λ n → isPropDec (isProp⟨≤⟩)))
                 (λ n → yes ≤-zero)
                 succCase
                 (λ ih n → no λ p → <-irreflexive _ (<∘≤-in-< (ι n <lim) p))
  where
  succCase : {x : Brw} → ((n : ℕ) → Dec (x ≤ ι n)) → (n : ℕ) → Dec (succ x ≤ ι n)
  succCase ih zero = no λ p → <-irreflexive _ (≤∘<-in-< p zero<succ)
  succCase ih (suc n) = mapDec ≤-succ-mono (λ p q → p (≤-succ-mono⁻¹ q)) (ih n)

dec-n< : (x : Brw) → (n : ℕ) → Dec (ι n < x)
dec-n< x n = dec-n≤ x (suc n)

dec-<n : (x : Brw) → (n : ℕ) → Dec (x < ι n)
dec-<n x n = dec-≤n (succ x) n

Dec<ω : ∀ x → Dec (x < ω)
Dec<ω x = mapDec (fst (isFinite-correct₂ x))
                 (λ q x<ω → q (snd (isFinite-correct₂ x) x<ω))
                 (decIsFinite x)

<ω⊎≥ω : (x : Brw) → (x < ω) ⊎ (ω ≤ x)
<ω⊎≥ω x with Dec<ω x
... | yes p  = inl p
... | no ¬p = inr (notFinite→ω≤ x λ p → ¬p (fst (isFinite-correct₂ x) p) )
