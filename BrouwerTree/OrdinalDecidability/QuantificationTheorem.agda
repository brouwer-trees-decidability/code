{-# OPTIONS --cubical --erasure --guardedness  #-}
module BrouwerTree.OrdinalDecidability.QuantificationTheorem where

open import PropTrunc
open import Cubical.Data.Nat
  using (ℕ; zero; suc; ·-comm ; max ; +-zero ; +-suc ; isSetℕ)
  renaming (_+_ to _N+_; _·_ to _N·_; +-assoc to N+-assoc)
import Cubical.Data.Nat.Order as N
import Cubical.Data.Nat.Properties as N
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import PropTrunc
open import BrouwerTree.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Fin.Base
open import Cubical.Data.FinData.Base renaming  (Fin to FinData ; toℕ to toℕ-FinData ; fromℕ to fromℕ-FinData )
open import Cubical.Data.FinData.Properties
open import BrouwerTree.OrdinalDecidability.Basic
open import BrouwerTree.OrdinalDecidability.GeneralProperties
open import BrouwerTree.OrdinalDecidability.MinFunctionRel
open import BrouwerTree.OrdinalDecidability.MaxFunctionRel
open import BrouwerTree.OrdinalDecidability.QuantificationConstruction
open import BrouwerTree.OrdinalDecidability.QuantificationLemmas
open import BrouwerTree.OrdinalDecidability.QuantificationCut

open import Iff

private
 variable
  ℓ : Level

monotone-if-up-closed
 : (P : ℕ → Type ℓ)
 → up-closed P
 → (n m : ℕ) → n N.≤ m → P n → P m
monotone-if-up-closed P P-up-c _ _ (k , e) = h k e
 where
  h : {n m : ℕ} (k : ℕ) → k N+ n ≡ m → P n → P m
  h zero e p = subst P e p
  h {n} {m} (suc k) e p = subst P e (P-up-c (k N+ n) (h k refl p))

---------------------------------------------------------------------------------------
---------------------PART 3 : For semidecidable P : ℕ → hprop, ∀n.P is ω²-deciable.
---------------------------------------------------------------------------------------

Pₙ-ωdec→∀nPₙ-ω²dec-downclosed : (P : ℕ → Type ℓ) →
                                ((n : ℕ) → isProp (P n) ) →
                                down-closed P →
                                ((n : ℕ) → semi-dec (P n)) →
                                (ordinal-dec-str (ω · ω) ( ∀ (n : ℕ) → (P n)))
Pₙ-ωdec→∀nPₙ-ω²dec-downclosed P Pprop Pdownclosed Psemidec =
 (characteristic-ordinal P Psemidec , characteristic-ordinal-characterisation P Psemidec Pprop Pdownclosed)

---------------------------------------
module down-closed
        (Q : ℕ → Type ℓ)
       where
 T : ℕ → Type ℓ
 T zero = Q zero
 T (suc n) = T n × Q (suc n)


 T-down-closed : (n : ℕ) → T (suc n) → T n
 T-down-closed zero  t = fst t
 T-down-closed (suc n)  t = fst t

 T-is-prop : ((n : ℕ) → isProp (Q n))
           → (n : ℕ) → isProp (T n)
 T-is-prop i zero  = i zero
 T-is-prop i (suc n)  = isProp× (T-is-prop i n) (i (suc n) )

 T-semi-dec
  : ((n : ℕ) → semi-dec (Q n ))
  → ((n : ℕ) → semi-dec (T n))
 T-semi-dec σ zero = σ zero
 T-semi-dec σ (suc n) =
  ∧-semi-dec (T n) (Q (suc n)) (T-semi-dec σ n) (σ (suc n))

 T-ord-dec
  : (α : Brw)
  → ((n : ℕ) → isProp (Q n))
  → ((n : ℕ) → ordinal-dec α (Q n ))
  → ((n : ℕ) → ordinal-dec α (T n))
 T-ord-dec α Q-prop σ zero = σ zero
 T-ord-dec α Q-prop σ (suc n) = ordinal-dec-× (T n) (Q (suc n))
                                              (T-is-prop Q-prop n)
                                              (Q-prop (suc n))
                                              α
                                              (T-ord-dec α Q-prop σ n)
                                              (σ (suc n))

 T-stronger : (n : ℕ) → T n → Q n
 T-stronger zero q = q
 T-stronger (suc n) (t , q) = q

 T-equivalent-∀
  :  (∀ n → T n) ↔ (∀ n → Q n)
 T-equivalent-∀  = [1] , [2]
  where
   [1] : ((n : ℕ) → T n) → (n : ℕ) → Q n
   [1] h n = T-stronger n (h n)
   [2] : ((n : ℕ) → Q n) → (n : ℕ) → T n
   [2] h zero = h 0
   [2] h (suc n) = ([2] h n) , h (suc n)

module up-closed
        (Q : ℕ → Type ℓ)
       where
 T : ℕ → Type ℓ
 T zero = Q zero
 T (suc n) = ∥ T n ⊎ Q (suc n) ∥

 T-up-closed : (n : ℕ) → T n → T (suc n)
 T-up-closed zero t = ∣ inl t ∣
 T-up-closed (suc n) t = ∥-∥map (inl ∘ ∣_∣) t

 T-is-prop : ((n : ℕ) → isProp (Q n))
           → (n : ℕ) → isProp (T n)
 T-is-prop i zero  = i zero
 T-is-prop i (suc n)  = isPropPropTrunc

 T-ord-dec
  : (k n : ℕ)
  → ((i : ℕ) → isProp (Q i))
  → ((i : ℕ) → ordinal-dec (ω · ι k + ι n) (Q i))
  → ((i : ℕ) → ordinal-dec (ω · ι k + ι n) (T i))
 T-ord-dec k n Q-prop σ zero = σ zero
 T-ord-dec k n Q-prop σ (suc i) = ordinal-dec-∨ k n (T i) (Q (suc i))
                                                (T-is-prop Q-prop i)
                                                (Q-prop (suc i))
                                                (T-ord-dec k n Q-prop σ i)
                                                (σ (suc i))

 T-semi-dec : ((n : ℕ) → semi-dec (Q n)) → ((n : ℕ) → semi-dec (T n))
 T-semi-dec σ zero = σ zero
 T-semi-dec σ (suc n) =
  ∨-semi-dec (T n) (Q (suc n)) (T-semi-dec σ n) (σ (suc n))

 T-weaker : (n : ℕ) → Q n → T n
 T-weaker zero q = q
 T-weaker (suc n) q = ∣ inr q ∣

 T-equivalent-∃ : ∃[ n ∈ ℕ ] T n ↔ ∃[ n ∈ ℕ ] Q n
 T-equivalent-∃  = (∥-∥rec isPropPropTrunc (uncurry [1])) , ∥-∥map [2]
  where
   [1] : (n : ℕ) → T n → ∃[ n ∈ ℕ ] Q n
   [1] zero q = ∣ 0 , q ∣
   [1] (suc n) t = ∥-∥rec isPropPropTrunc [1]' t
    where
     [1]' : {n : ℕ} → T n ⊎ Q (suc n) → ∃[ n ∈ ℕ ] Q n
     [1]' {n} (inl t) = [1] n t
     [1]' {n} (inr q) = ∣ suc n , q ∣

   [2] : Σ[ n ∈ ℕ ] Q n → Σ[ n ∈ ℕ ] T n
   [2] (n , q) = n , T-weaker n q

----------------------------------------------

Pₙ-ωdec→∀nPₙ-ω²dec : (P : ℕ → Type ℓ)
                   → ((n : ℕ) → isProp (P n) )
                   → ((n : ℕ) → semi-dec (P n))
                   → ordinal-dec-str (ω · ω) (∀ (n : ℕ) → (P n))
Pₙ-ωdec→∀nPₙ-ω²dec P Pprop Psemidec  =
 lr (ordinal-dec-str-stable-under-↔
      (∀ (n : ℕ) →  T n) (∀ (n : ℕ) → P n)
      (down-closed.T-equivalent-∀ P))
    (Pₙ-ωdec→∀nPₙ-ω²dec-downclosed T Tprop Tdownclosed Tsemidec)
  where
   T = down-closed.T P
   Tprop = down-closed.T-is-prop P Pprop
   Tsemidec = down-closed.T-semi-dec P Psemidec
   Tdownclosed = down-closed.T-down-closed P


---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------
------------------ PART II : ∃n P(n) For Semidecdiable P : ℕ → Prop-------------------------

-- Theorem: Countable join of semidecidable propositions is decidable in ω·3 steps

----------------------------------
characteristic-ordinal-existential
 : (P : ℕ → Type ℓ)
 → (Psemidec : (n : ℕ) → semi-dec (P n))
 → ((n : ℕ) → isProp (P n))
 → ∃ ℕ P  ↔ (ω + ω) + ω ≤ characteristic-ordinal P Psemidec
characteristic-ordinal-existential P Psemidec Pprop = ∃nPn→ω·3≤limF , ω·3≤limF→∃nPn
 where
  F : ℕ → Brw
  F = characteristic-sequence P Psemidec
  F↑ : increasing F
  F↑ = characteristic-sequence-increasing P  Psemidec

  ∃nPn→ω·3≤limF' : Σ ℕ P → ((ω + ω) + ω) ≤ limit F {F↑}
  ∃nPn→ω·3≤limF' (n , Pn)  = weakly-bisimilar→lim≤lim (λ k → (ω + ω) + ι k) F
                            (λ k → ∣ (suc n) N+ k ,
                            ≤-trans (+-mono {y = ι k} {y' = ι k} β ≤-refl)
                            (add-finite-part-lemma' F {F↑} (suc n) k) ∣)
     where
      β : ω + ω ≤ F (suc n)
      β = ≤-trans (characteristic-ordinal-up-to-above-ω·2 P Psemidec n Pn) Gsn≤Fsn
       where
        G : ℕ → Brw
        G n =  (P characteristic-ordinal-up-to n) (λ i → (λ p → Psemidec i))
        Gsn≤Fsn :  G (suc n) ≤ F (suc n)
        Gsn≤Fsn = x+-mono {_} {zero} {ι (suc n)} ≤-zero


  ∃nPn→ω·3≤limF : ∃ ℕ P → ((ω + ω) + ω) ≤ limit F {F↑}
  ∃nPn→ω·3≤limF  = ∥-∥rec ≤-trunc ∃nPn→ω·3≤limF'
  ---------------------

  ω·3≤limF→∃nPn :  ((ω + ω) + ω) ≤ limit F {F↑} → ∃ ℕ P
  ω·3≤limF→∃nPn ω·3≤limF = lr (characteristic-ordinal-up-to-spec P Psemidec) [1]
   where
    G : ℕ → Brw
    G n =  (P characteristic-ordinal-up-to n) (λ i → (λ p → Psemidec i))
    [1] : ∃[ n ∈ ℕ ] ω + ω ≤ G n
    [1] = [2] (lim≤lim→weakly-bisimilar (λ n → (ω + ω) + ι n) F  ω·3≤limF 0)
     where
      [2] : ∃[ m ∈ ℕ ] ω + ω ≤ F m → ∃[ m ∈ ℕ ] ω + ω ≤ G m
      [2] = ∥-∥map (map-snd (λ {m} hm → cancel-finite-limit-≤ (λ n → ω + ι n) (G m) m hm))

----------------------------


Pₙ-ωdec→∃nPₙ-ω·3dec : (P : ℕ → Type ℓ)
                     → ((n : ℕ) → isProp (P n))
                     → ((n : ℕ) → semi-dec (P n))
                     → ordinal-dec-str ((ω + ω) + ω) (∃ ℕ P)
Pₙ-ωdec→∃nPₙ-ω·3dec P Pprop Psemidec =
  characteristic-ordinal P Psemidec , characteristic-ordinal-existential P Psemidec Pprop

Pₙ-ωdec→∃nPₙ-ω·3dec' : (P : ℕ → Type ℓ)
                      → ((n : ℕ) → isProp (P n))
                      → ((n : ℕ) → semi-dec (P n))
                      → ordinal-dec-str (ω · (ι 3)) (∃ ℕ P)
Pₙ-ωdec→∃nPₙ-ω·3dec' P Pprop Psemidec =
 subst (λ - → ordinal-dec-str - (∃ ℕ P))
       (sym (x·3=x+x+x ω))
       (Pₙ-ωdec→∃nPₙ-ω·3dec P Pprop Psemidec)


-------------------------------------------------------

module up-down-closed
        (Q : ℕ → ℕ → Type ℓ)
       where

 T : ℕ → ℕ → Type ℓ
 T zero m = Q zero m
 T (suc n) m = T n m × Q (suc n) m

 T-up-closed :
  ((n m : ℕ) → Q n m → Q n (suc m))
  → (n m : ℕ) → T n m → T n (suc m)
 T-up-closed Q-up-c zero m = Q-up-c zero m
 T-up-closed Q-up-c (suc n) m (t , q) =
  (T-up-closed Q-up-c n m t) , (Q-up-c (suc n) m q)

 T-down-closed : (n m : ℕ) → T (suc n) m → T n m
 T-down-closed zero m t = fst t
 T-down-closed (suc n) m t = fst t

 T-is-prop : ((n m : ℕ) → isProp (Q n m))
           → (n m : ℕ) → isProp (T n m)
 T-is-prop i zero m = i zero m
 T-is-prop i (suc n) m = isProp× (T-is-prop i n m) (i (suc n) m)

 T-semi-dec
  : ((n m : ℕ) → semi-dec (Q n m))
  → ((n m : ℕ) → semi-dec (T n m))
 T-semi-dec σ zero m = σ zero m
 T-semi-dec σ (suc n) m =
  ∧-semi-dec (T n m) (Q (suc n) m) (T-semi-dec σ n m) (σ (suc n) m)

 T-stronger : (n m : ℕ) → T n m → Q n m
 T-stronger zero m q = q
 T-stronger (suc n) m (t , q) = q

 T-equivalent-∀∃
  : ((n m : ℕ) → Q n m → Q n (suc m))
  → (∀ n → ∃[ m ∈ ℕ ] T n m) ↔ (∀ n → ∃[ m ∈ ℕ ] Q n m)
 T-equivalent-∀∃ Q-up-c = [1] , [2]
  where
   [1] : ((n : ℕ) → ∃ ℕ (T n)) → (n : ℕ) → ∃ ℕ (Q n)
   [1] h n = ∥-∥map (λ (m , t) → m , T-stronger n m t) (h n)
   [2] : ((n : ℕ) → ∃ ℕ (Q n)) → (n : ℕ) → ∃ ℕ (T n)
   [2] h zero = ∥-∥map (λ (m , q) → m , q) (h 0)
   [2] h (suc n) = ∥-∥map2 [3] IH (h (suc n))
    where
     IH : ∃ ℕ (T n)
     IH = [2] h n
     [3] : Σ ℕ (T n) → Σ ℕ (Q (suc n)) → Σ ℕ (T (suc n))
     [3] (m , t) (k , q) =
      M ,
      monotone-if-up-closed (T n) (T-up-closed Q-up-c n) m M N.left-≤-max t ,
      monotone-if-up-closed (Q (suc n)) (Q-up-c (suc n)) k M (N.right-≤-max {k} {m}) q
       where
        M = max m k

 T-equivalent-∃∀
  : ∃[ m ∈ ℕ ] (∀ n → T n m) ↔ ∃[ m ∈ ℕ ] (∀ n → Q n m)
 T-equivalent-∃∀ = (∥-∥map [1] , ∥-∥map [2])
  where
   [1] : Σ ℕ (λ m → ∀ n → T n m) → Σ ℕ (λ m → ∀ n → Q n m)
   [1] (m , t) = (m , λ n → T-stronger n m (t n))
   [2] : Σ ℕ (λ m → ∀ n → Q n m) → Σ ℕ (λ m → ∀ n → T n m)
   [2] (m , q) = (m , t)
    where
     t : (n : ℕ) → T n m
     t zero = q 0
     t (suc n) = t n , q (suc n)

∃∀Semidec : (P : ℕ → ℕ → Type ℓ) →
            (∀ (n m : ℕ) →  isProp (P n m))
          → (∀ (n m : ℕ) →  semi-dec (P n m))
          → (∀ (n m : ℕ) → P n m → P n (suc m))
          → ordinal-dec-str (ω² + ω) (∃[ m ∈ ℕ ] ∀ (n : ℕ) → P n m)
∃∀Semidec {ℓ} P P-prop P-semi-dec P-up-c-2 =
 lr (ordinal-dec-str-stable-under-↔ _ _ Q-equivalent-∀∃) [8]
 where
  Q : ℕ → ℕ → Type ℓ
  Q = up-down-closed.T P

  Q-down-c-1 : (n m : ℕ) → Q (suc n) m → Q n m
  Q-down-c-1 = up-down-closed.T-down-closed P

  Q-up-c-2 : (n m : ℕ) → Q n m → Q n (suc m)
  Q-up-c-2 = up-down-closed.T-up-closed P P-up-c-2

  Q-semi-dec : (n m : ℕ) → semi-dec (Q n m)
  Q-semi-dec = up-down-closed.T-semi-dec P P-semi-dec

  Q-equivalent-∀∃ : ∃[ m ∈ ℕ ] (∀ n → Q n m) ↔ ∃[ m ∈ ℕ ] (∀ n → P n m)
  Q-equivalent-∀∃ = up-down-closed.T-equivalent-∃∀ P

  Q-prop : (n m : ℕ) → isProp (Q n m)
  Q-prop = up-down-closed.T-is-prop P P-prop

  f : ℕ → ℕ → Brw
  f m = characteristic-sequence (λ n → Q n m) (λ n → Q-semi-dec n m)

  f-characterisation : (m : ℕ) → (((n : ℕ) → Q n m) ↔ ω² ≤ limit (f m))
  f-characterisation m =
   characteristic-ordinal-characterisation (λ n → Q n m)
                                           (λ n → Q-semi-dec n m)
                                           (λ n → Q-prop n m)
                                           (λ n → Q-down-c-1 n m)

  lim⟨f⁻⟩-increasing-≤ : (m : ℕ) → limit (f m) ≤ limit (f (suc m))
  lim⟨f⁻⟩-increasing-≤ m =
   characteristic-ordinal-mono
    (λ n → Q n m)
    (λ n → Q n (suc m))
    (λ n → Q-up-c-2 n m)
    (λ n → Q-semi-dec n m)
    (λ n → Q-semi-dec n (suc m))

  lim⟨f⁻⟩-monotone : (m n : ℕ) → m N.≤ n → limit (f m) ≤ limit (f n)
  lim⟨f⁻⟩-monotone m n = increasing-≤→monotone (lim⟨f⁻⟩-increasing-≤)

  θ : ℕ → Brw
  θ k = characteristic-ordinal (λ n → Q n k) (λ n → Q-semi-dec n k) + ι k

  θ↑ : increasing θ
  θ↑ k = ≤∘<-in-< (+-mono {y = ι k} (lim⟨f⁻⟩-increasing-≤ k) ≤-refl) (x+-mono-< (ι-increasing k))

  [1] : ∃[ m ∈ ℕ ] (∀ n → Q n m) → ω² + ω ≤ limit θ
  [1] = ∥-∥rec isProp⟨≤⟩ [1]'
   where
    [1]' : Σ[ m ∈ ℕ ] (∀ n  → Q n m) → ω² + ω ≤ limit θ
    [1]' (m , q) = simulation→≤ (λ k → m N+ k , ≤-trans ([2] k) ([3] k))
     where
      [2] : (k : ℕ) → ω² + ι k ≤ limit (f m) + ι k
      [2] k = +-mono {y = ι k} (lr (f-characterisation m) q) ≤-refl
      [3] : (k : ℕ) → limit (f m) + ι k ≤ limit (f (m N+ k)) + ι (m N+ k)
      [3] k = +-mono {y = ι k} (lim⟨f⁻⟩-monotone m (m N+ k) N.≤SumLeft) (ι-mono (N.≤SumRight {k = m}))

  [4] : ω² + ω ≤ limit θ → ∃[ m ∈ ℕ ] (∀ n → Q n m)
  [4] l = ∥-∥map (λ (m , p) → (m , rl (f-characterisation m) p)) [7]
   where
    [5] : (λ n → ω² + ι n) ≲ (λ k → limit (f k) + ι k)
    [5] = lim≤lim→weakly-bisimilar (λ n → ω² + ι n) θ l
    [6] : ∃[ n ∈ ℕ ] ω² ≤ limit (f n) + ι n
    [6] = [5] 0
    [7] : ∃[ n ∈ ℕ ] ω² ≤ limit (f n)
    [7] = ∥-∥map (λ (n , p) → n , cancel-finite-limit-≤ (λ n → ω · ι n) (limit (f n)) n p) [6]

  [8] : ordinal-dec-str (ω² + ω) (∃[ m ∈ ℕ ] (∀ n → Q n m))
  [8] =  limit θ {θ↑} , [1] , [4]
