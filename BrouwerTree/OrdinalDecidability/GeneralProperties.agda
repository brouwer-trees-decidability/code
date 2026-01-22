{-# OPTIONS --cubical --erasure --guardedness  #-}
module BrouwerTree.OrdinalDecidability.GeneralProperties where

open import Cubical.Data.Nat
  using (ℕ; zero; suc; +-zero ; +-suc ; +-comm; isSetℕ)
  renaming (_+_ to _N+_)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import PropTrunc
open import Iff

open import BrouwerTree.Everything

open import BrouwerTree.OrdinalDecidability.Basic

private
 variable
  ℓ ℓ' : Level

ordinal-dec-str-stable-under-↔ : {α : Brw} (P : Type ℓ) (Q : Type ℓ')
                               → (P ↔ Q)
                               → ordinal-dec-str α P ↔ ordinal-dec-str α Q
ordinal-dec-str-stable-under-↔ {α = α} P Q (f , g) =
 [1] P Q f g , [1] Q P g f
  where
   [1] : (P : Type ℓ) (Q : Type ℓ') → (P → Q) → (Q → P)
       → ordinal-dec-str α P → ordinal-dec-str α Q
   [1] P Q f g (β , (d₀ , d₁)) = (β , (d₀ ∘ g , f ∘ d₁))

ordinal-dec-stable-under-↔ : {α : Brw} (P : Type ℓ) (Q : Type ℓ')
                           → (P ↔ Q) → ordinal-dec α P ↔ ordinal-dec α Q
ordinal-dec-stable-under-↔ {α} P Q e =
 (∥-∥map (lr (ordinal-dec-str-stable-under-↔ P Q e)) ,
  ∥-∥map (rl (ordinal-dec-str-stable-under-↔ P Q e)))

-------------------------------------------------------------
-- Ordinal decidability is downward closed over successors:

ordinal-dec-downward-closed-succ : (P : Type ℓ) {x : Brw}
                                 → (n : ℕ) → n N.> 0
                                 → ordinal-dec (succ (x + ι n)) P
                                 → ordinal-dec (x + ι n) P
ordinal-dec-downward-closed-succ P {x} n n-pos@(k , k-eq) =
 ∥-∥rec isPropPropTrunc (λ (u , q) → [1] u q)
 where
  [1] : (u : Brw) → (P ↔ succ (x + ι n) ≤ u) → ordinal-dec (x + ι n) P
  [1] = Brw-ind _ (λ u → isPropΠ (λ _ → isPropPropTrunc)) Q₀ Qₛ Qₗ
   where
    Q₀ : P ↔ (succ (x + ι n) ≤ zero) → ordinal-dec (x + ι n) P
    Q₀ (impl₁ , impl₂) =
     ∣ zero ,
       (λ p → ⊥.rec (succ≰zero (impl₁ p))) ,
       (λ l → ⊥.rec (ι≰zero n n-pos (≤-trans (+x-increasing (ι n)) l))) ∣
    Qₛ : {y : Brw}
       → (P ↔ (succ (x + ι n) ≤ y) → ordinal-dec (x + ι n) P )
       → P ↔ (succ (x + ι n) ≤ succ y)
       → ordinal-dec (x + ι n) P
    Qₛ {y} _ (impl₁ , impl₂) =
     ∣ y , (λ p → ≤-succ-mono⁻¹ (impl₁ p)) , (λ l → impl₂ (≤-succ-mono l)) ∣
    Qₗ : {g : ℕ → Brw} {g↑ : increasing g}
       → ((k : ℕ) → P ↔ (succ (x + ι n) ≤ g k) → ordinal-dec (x + ι n) P)
       → P ↔ (succ (x + ι n) ≤ limit g {g↑})
       → ordinal-dec (x + ι n) P
    Qₗ {g} {g↑} IH (impl₁ , impl₂) = ∣ limit g , [2] , [3] ∣
     where
      [2] : P → (x + ι n) ≤ limit g {g↑}
      [2] p = ≤-trans ≤-succ-incr-simple (impl₁ p)
      [3] : (x + ι n) ≤ limit g → P
      [3] l = impl₂ ([4] k e)
       where
        e = n          ≡⟨ sym k-eq ⟩
            k N+ 1     ≡⟨ +-suc k 0 ⟩
            suc k N+ 0 ≡⟨ +-zero (suc k) ⟩
            suc k      ∎
        [4] : (k : ℕ) → n ≡ suc k → x + ι n < limit g
        [4] k e = subst (_< limit g)
                        (cong (λ - → x + ι -) (sym e))
                        (x<lim→sx<lim g (x + ι k) l')
         where
          l' : succ (x + ι k) ≤ limit g
          l' = subst (_≤ limit g) (cong (λ - → x + ι -) e) l

------------------------
-- Ordinal Decidability is invariant over finite successors

ordinal-dec-equivalent-finite-successors
 : (P : Type ℓ) → {x : Brw} → (n : ℕ)
 → ordinal-dec (x + ι 1) P ↔ ordinal-dec (x + ι (suc n)) P
ordinal-dec-equivalent-finite-successors P {x} n = ([1] n , [3] n)
 where
  [1] : (n : ℕ) → ordinal-dec (x + ι 1) P → ordinal-dec (x + ι (suc n)) P
  [1] zero d = d
  [1] (suc n) d = ∥-∥map [2] ([1] n d)
   where
    [2] : Σ[ z ∈ Brw ] (P ↔ x + (ι n) < z) → Σ[ w ∈ Brw ] (P ↔ (x + (ι (suc n)) < w))
    [2] (z , (gₗ , gᵣ)) = succ z , (hₗ , hᵣ)
     where
      hₗ : P → succ (x + ι n) < succ z
      hₗ p = <-succ-mono (gₗ p)

      hᵣ : succ (x + ι n) < succ z → P
      hᵣ q = gᵣ (<-succ-mono⁻¹ q)

  [3] : (n : ℕ) → ordinal-dec (x + ι (suc n)) P → ordinal-dec (x + ι 1) P
  [3] zero d = d
  [3] (suc n) d =
   [3] n (ordinal-dec-downward-closed-succ P (suc n) (n , +-comm n 1) d)

-------------------------
-- The rounding up function (⇑) gives the least upper limit

⇑ : Brw → Brw
⇑ zero = zero
⇑ (succ x) = x + ω
⇑ (limit f {f↑}) = limit f {f↑}
⇑ (bisim f {f↑} g {g↑} x i) =  bisim f {f↑} g {g↑} x i
⇑ (trunc x y p q i j) =  trunc (⇑ x) (⇑ y) (cong ⇑ p) (cong ⇑ q) i j

⇑-is-lim : (x : Brw) → is-lim (⇑ x) ⊎ (x ≡ zero)
⇑-is-lim = Brw-ind _ i P₀ Pₛ Pₗ
 where
  i : (x : Brw) → isProp (is-lim (⇑ x) ⊎ (x ≡ zero))
  i x = isProp⊎ isPropPropTrunc
                (Brw-is-set x zero)
                (λ l e → unique.not-z-and-l (⇑ x) (≡zero→is-zero (cong ⇑ e)) l)
  P₀ : is-lim (⇑ zero) ⊎ (zero ≡ zero)
  P₀ = inr refl
  Pₛ : {x : Brw}
     → is-lim (⇑ x) ⊎ (x ≡ zero)
     → is-lim (limit (λ n → x + ι n)) ⊎ (succ x ≡ zero)
  Pₛ _ = inl (is-lim-limit _ _)
  Pₗ : {f : ℕ → Brw} {f↑ : increasing f}
     → ((k : ℕ) → is-lim (⇑ (f k)) ⊎ (f k ≡ zero))
     → is-lim (limit f {f↑}) ⊎ (limit f {f↑} ≡ zero)
  Pₗ _ = inl (is-lim-limit _ _)

⇑-Islim⊎zero : (x : Brw) → Brw-zero-or-limit (⇑ x)
⇑-Islim⊎zero x = h (⇑-is-lim x)
 where
  h : is-lim (⇑ x) ⊎ (x ≡ zero) → Brw-zero-or-limit (⇑ x)
  h (inl l) = inl l
  h (inr z) = inr (subst (λ - → ⇑ - ≡ zero) (sym z) refl)

⇑ᶻˡ : Brw → Brwᶻˡ
⇑ᶻˡ x = ⇑ x , ⇑-Islim⊎zero x

⇑-succ : (x : Brw) → ⇑ (succ x) ≡ ⇑ (succ (succ x))
⇑-succ x = bisim _ _ (h₀ , h₁)
 where
  h₀ : (λ n → x + ι n) ≲ (λ n → succ x + ι n)
  h₀ n = ∣ n , +-mono {x = x} {y = ι n} ≤-succ-incr-simple ≤-refl ∣

  h₁ : (λ n → succ x + ι n) ≲ (λ n → x + ι n)
  h₁ n = ∣ (suc n) , ≤-refl-≡ (ι-succ x n) ∣

⇑-monotone : (x y : Brw) → x ≤ y → ⇑ x ≤ ⇑ y
⇑-monotone =
 Brw-ind (λ x → (y : Brw) → x ≤ y → ⇑ x ≤ ⇑ y)
         (λ x → isPropΠ2 (λ _ _ → ≤-trunc))
         P₀ Pₛ Pₗ
  where
   P₀ : (y : Brw) → zero ≤ y → ⇑ zero ≤ ⇑ y
   P₀ y _ = ≤-zero
   Pₛ : {x : Brw}
      → ((y : Brw) → x ≤ y → ⇑ x ≤ ⇑ y)
      → (y : Brw) → succ x ≤ y → x + ω ≤ ⇑ y
   Pₛ {x} _ = Brw-ind _ (λ _ → isProp→ ≤-trunc) Q₀ Qₛ Qₗ
    where
     Q₀ : succ x ≤ zero → limit (λ n → x + ι n) ≤ zero
     Q₀ l = ⊥.elim (succ≰zero l)
     Qₛ : {y : Brw}
        → (succ x ≤ y → x + ω ≤ ⇑ y)
        → succ x ≤ succ y
        → x + ω ≤ y + ω
     Qₛ {y} _ l = +x-mono ω (≤-succ-mono⁻¹ l)
     Qₗ : {f : ℕ → Brw} {f↑ : increasing f}
        → ((k : ℕ) → succ x ≤ f k → x + ω ≤ ⇑ (f k))
        → succ x ≤ limit f {f↑} → x + ω ≤ limit f {f↑}
     Qₗ {f} {f↑} _ l = ≤-limiting (λ n → x + ι n) q
      where
       q : (k : ℕ) → x + ι k ≤ limit f
       q zero = ≤-trans ≤-succ-incr-simple l
       q (suc zero) = l
       q (suc (suc k)) = x<lim→sx<lim f (x + ι k) (q (suc k))
   Pₗ : {f : ℕ → Brw} {f↑ : increasing f}
      → ((k : ℕ) (y : Brw) → f k ≤ y → ⇑ (f k) ≤ ⇑ y)
      → (y : Brw) → limit f {f↑} ≤ y → limit f {f↑} ≤ ⇑ y
   Pₗ {f} {f↑} _ = Brw-ind _ (λ _ → isProp→ ≤-trunc) Q₀ Qₛ Qₗ
    where
     Q₀ : limit f ≤ zero → limit f ≤ ⇑ zero
     Q₀ l = ⊥.elim (lim≰zero l)
     Qₛ : {y : Brw}
        → (limit f ≤ y → limit f ≤ ⇑ y)
        → limit f ≤ succ y → limit f ≤ y + ω
     Qₛ {y} _ l = ≤-cocone (λ n → y + ι n) {_} {0} (lim≤sx→lim≤x f (y + ι 0) l)
     Qₗ : {g : ℕ → Brw} {g↑ : increasing g}
        → ((k : ℕ) → limit f {f↑} ≤ g k → limit f {f↑} ≤ ⇑ (g k))
        → limit f {f↑} ≤ limit g {g↑} → limit f ≤ limit g
     Qₗ {g} {g↑} _ l = l

⇑-left-≤ : (y : Brw) → Brw-zero-or-limit y → (x : Brw) → x ≤ y ↔ ⇑ x ≤ y
⇑-left-≤ y y-zl =
 Brw-ind _ (λ _ → isProp↔ ≤-trunc ≤-trunc) ↔-refl [1] (λ _ → ↔-refl)
  where
   [1] : {x : Brw}
     → x ≤ y ↔ ⇑ x ≤ y
     → succ x ≤ y ↔ x + ω ≤ y
   [1] {x} _ = [2] y-zl
    where
     [2] : is-lim y ⊎ (y ≡ zero) → succ x ≤ y ↔ x + ω ≤ y
     [2] (inr y-zero) = (λ l → ⊥.elim (succ≰zero (subst (succ x ≤_) y-zero l))) ,
                        (λ l → ⊥.elim (lim≰zero (subst (x + ω ≤_) y-zero l)))
     [2] (inl y-lim ) =
      reduce-to-canonical-limits (λ y' → succ x ≤ y' ↔ x + ω ≤ y')
                                 (λ y' → isProp↔ ≤-trunc ≤-trunc)
                                 [3] y y-lim
       where
        [3] : (f : ℕ → Brw) (f↑ : increasing f)
            → succ x ≤ limit f ↔ x + ω ≤ limit f
        [3] f f↑ = [5] , [4]
         where
          [4] : x + ω ≤ limit f → succ x ≤ limit f
          [4] l = x + ι 1  ≤⟨ ≤-cocone-simple (λ n → x + ι n) {_} {1} ⟩
                  x + ω    ≤⟨ l ⟩
                  limit f  ≤∎
          [5] : succ x ≤ limit f → x + ω ≤ limit f
          [5] l = ∥-∥rec ≤-trunc [6] (below-limit-lemma x f l)
           where
            [6] : Σ ℕ (λ n → x < f n) → x + ω ≤ limit f
            [6] (n , u) = ≤-limiting (λ k → x + ι k) [7]
             where
              [7] : (k : ℕ) → x + ι k ≤ limit f
              [7] k = x + ι k    ≤⟨ ≤-offset-by-ι f {f↑} x (<-in-≤ u) ⟩
                      f (n N+ k) ≤⟨ ≤-cocone-simple f ⟩
                      limit f    ≤∎

⇑-right-≤ : (y : Brw) → Brw-zero-or-limit y → (x : Brw)
          → succ y ≤ x ↔ succ y ≤ ⇑ x
⇑-right-≤ y y-zl =
 Brw-ind _ (λ _ → isProp↔ ≤-trunc ≤-trunc) ↔-refl [1] (λ _ → ↔-refl)
  where
   [1] : {x : Brw}
       → succ y ≤ x ↔ succ y ≤ ⇑ x
       → succ y ≤ succ x ↔ succ y ≤ x + ω
   [1] {x} _ = ↔-trans (≤-succ-mono⁻¹ , ≤-succ-mono)
                       ([2] , [3] y-zl)
    where
     [2] : y ≤ x → succ y ≤ x + ω
     [2] l = ≤-trans (≤-succ-mono l) (≤-cocone-simple (λ n → x + ι n) {_} {1})
     [3] : is-lim y ⊎ (y ≡ zero) → succ y ≤ x + ω → y ≤ x
     [3] (inl y-lim ) l =
      ∥-∥rec ≤-trunc [4] (below-limit-lemma y (λ n → x + ι n) l)
       where
        [4] : Σ ℕ (λ n → y < x + ι n) → y ≤ x
        [4] (n , u) = cancel-finite-lim-≤ y x y-lim n (<-in-≤ u)
     [3] (inr y-zero) _ = subst (_≤ x) (sym y-zero) ≤-zero

x≤⇑x : (x : Brw) → x ≤ ⇑ x
x≤⇑x = Brw-ind (λ x → x ≤ ⇑ x) (λ x → isProp⟨≤⟩) ≤-refl (λ _ → τ) (λ _ → ≤-refl)
 where
  τ : {x : Brw} → x < x + ω
  τ {x} = x+-mono-< {y = zero} {ω} zero<ω

islim→⇑≡id : (x : Brw) → Brw-zero-or-limit x → ⇑ x ≡ x
islim→⇑≡id x (inl x-lim) =
 reduce-to-canonical-limits (λ x → ⇑ x ≡ x)
                            (λ x → Brw-is-set _ _)
                            (λ f _ → refl)
                            x x-lim
islim→⇑≡id x (inr x-zero) = subst (λ - → ⇑ - ≡ -) (sym x-zero) refl

------------------------------------------
-- Theorem: Any notion of ordinal decidability is equivalent to one with a
-- limit ordinal as benchmark ordinal

limit-<-x↔limit+ω-≤-⇑-x : (f : ℕ → Brw){f↑ : increasing f}(x : Brw)
                        → limit f {f↑} < x ↔ limit f {f↑} + ω ≤ ⇑ x
limit-<-x↔limit+ω-≤-⇑-x f {f↑} = Brw-ind _ [0] [1] [2] [3]
 where
  [0] : (x : Brw) → isProp (limit f {f↑} < x ↔ limit f {f↑} + ω ≤ ⇑ x)
  [0] x = isProp↔ isProp⟨<⟩ isProp⟨≤⟩

  [1] : (limit f < zero) ↔ (limit f + ω ≤ zero)
  [1] = (⊥.rec ∘ x≮zero , ⊥.rec ∘ lim≰zero)

  [2] : {x : Brw}
      → (limit f < x) ↔ (limit (λ n → limit f + ι n) ≤ ⇑ x)
      → (limit f < succ x) ↔ (limit f + ω ≤ x + ω)
  [2] {x} _ = [2]ₗ , [2]ᵣ
   where
    [2]ₗ : limit f < succ x → limit f + ω ≤ x + ω
    [2]ₗ l = +-mono {limit f} {ω} {x} {ω} (≤-succ-mono⁻¹ l) ≤-refl

    [2]ᵣ : limit f + ω ≤ x + ω → limit f < succ x
    [2]ᵣ l = ≤-succ-mono (limit-cancel-+ω-≤ x f {f↑} l)

  [3] : {g : ℕ → Brw} {g↑ : increasing g}
      → ((k : ℕ) → (limit f {f↑} < g k) ↔ (limit f {f↑} + ω ≤ ⇑ (g k)))
      → (limit f {f↑} < limit g {g↑}) ↔ (limit f {f↑} + ω ≤ limit g {g↑})
  [3] {g} {g↑} _ = ([3]ₗ , [3]ᵣ)
   where
    [3]ₗ : limit f {f↑} < limit g {g↑} → limit f {f↑} + ω ≤ limit g {g↑}
    [3]ₗ l = ∥-∥rec isProp⟨≤⟩ [5] [4]
     where
      [4] : ∃[ n ∈ ℕ ] limit f < g n
      [4] = below-limit-lemma (limit f) g l

      [5] : Σ[ n ∈ ℕ ] limit f < g n → limit f + ω ≤ limit g
      [5] (n , l') =
       simulation→≤ (λ m → (n N+ m) , ≤-trans ([6] m) ([7] m))
        where
         [6] : (m : ℕ) → (limit f + ι m) ≤ (g n + ι m)
         [6] m = +-mono {x = limit f} {y = ι m} (<-in-≤ l') ≤-refl
         [7] : (m : ℕ) → (g n + ι m) ≤ g (n N+ m)
         [7] m = add-finite-part-lemma' g {g↑} n m

    [3]ᵣ : limit f {f↑} + ω ≤ limit g {g↑} → limit f {f↑} < limit g {g↑}
    [3]ᵣ l = <∘≤-in-< (x+-mono-< zero<ω) l

ordinal-dec-equivalent-lim-benchmark
 : (P : Type ℓ) → isProp P → (x : Brw) → ordinal-dec x P  ↔ ordinal-dec (⇑ x) P
ordinal-dec-equivalent-lim-benchmark {ℓ} P p x = [1] x , [22] x
 where
  [1] : (x : Brw) → ordinal-dec x P → ordinal-dec (⇑ x) P
  [1] = Brw-ind Q i (λ d → d) [2] (λ _ d → d)
   where
    Q : (x : Brw) → Type ℓ
    Q x = ordinal-dec x P  → ordinal-dec (⇑ x) P
    i : (x : Brw) → isProp (Q x)
    i x = isPropΠ (λ _ → isPropPropTrunc)

    [2] : {x' : Brw} → Q x' → Q (succ x')
    [2] {x'} ih = Brw-ind (Q ∘ succ) (i ∘ succ) [3] [5] [7] x'
     where
      [3] : ordinal-dec (ι 1) P → ordinal-dec (⇑ (ι 1)) P
      [3] d = subst (λ - → ordinal-dec - P) [4] [3]'
       where
        [3]' : ordinal-dec ω P
        [3]' = lr (dec↔ω-dec P p)
                  (rl (dec↔fin-dec P p) (0 , d))

        [4] : ω ≡ ⇑ (ι 1)
        [4] = limit-pointwise-equal _ _ (λ n → sym (zero+y≡y (ι n)))

      [5] : {x'' : Brw} →  Q (succ x'') → Q (succ (succ x''))
      [5] {x''} ih' d = subst (λ - → ordinal-dec - P) (⇑-succ x'') [6]
       where
        [6] :  ordinal-dec (x'' + ω) P
        [6] = ih' (rl (ordinal-dec-equivalent-finite-successors P 1) d)

      [7] : {f : ℕ → Brw} {f↑ : increasing f}
          → ((k : ℕ) → Q (succ (f k))) → Q (succ (limit f {f↑}))
      [7] {f} {f↑} ih' d = ∥-∥map [7]' d
       where
        [7]' : ordinal-dec-str (succ (limit f)) P
             → ordinal-dec-str (limit f + ω) P
        [7]' (u , g) = ⇑ u , (P                 ↔⟨ g ⟩
                              limit f < u       ↔⟨ limit-<-x↔limit+ω-≤-⇑-x f u ⟩
                              limit f + ω ≤ ⇑ u ↔∎)
  [22] : (x : Brw) → ordinal-dec (⇑ x) P → ordinal-dec x P
  [22] = Brw-ind Q i (λ d → d) [8] (λ _  d → d)
   where
    Q : (x : Brw) → Type ℓ
    Q x = ordinal-dec (⇑ x) P → ordinal-dec x P
    i : (x : Brw) → isProp (Q x)
    i x = isPropΠ (λ _ → isPropPropTrunc)

    [8] : {x' : Brw} → Q x' → Q (succ x')
    [8] {x'} ih = Brw-ind (Q ∘ succ) (i ∘ succ) [9] [11] [13] x'
     where
      [9] : ordinal-dec (⇑ (ι 1)) P  → ordinal-dec (ι 1) P
      [9] d = lr (finite-decidability-all-equivalent P n 0) g
       where
        d' : ordinal-dec ω P
        d' = subst (λ - → ordinal-dec - P)
                   (limit-pointwise-equal _ _ (λ n → (zero+y≡y (ι n)))) d
        [10] : Σ[ n ∈ ℕ ] ordinal-dec (ι (suc n)) P
        [10] = lr (dec↔fin-dec P p) (rl (dec↔ω-dec P p) d')
        n = fst [10]
        g = snd [10]
      [11] : {y : Brw} → Q (succ y) → Q (succ (succ y))
      [11] {y} ih' d = lr (ordinal-dec-equivalent-finite-successors P 1) [12]
       where
        d' : ordinal-dec (⇑ (succ y)) P
        d' = subst (λ - → ordinal-dec - P ) (sym (⇑-succ y)) d
        [12] :  ordinal-dec (succ y) P
        [12] = ih' d'

      [13] : {f : ℕ → Brw} {f↑ : increasing f}
           → ((k : ℕ) → Q (succ (f k))) → Q (succ (limit f {f↑}))
      [13] {f} {f↑} ih' = ∥-∥rec isPropPropTrunc [14]
       where
        [14] : ordinal-dec-str (limit f + ω) P
             → ordinal-dec (succ (limit f)) P
        [14] (u , g) = Brw-ind Q' i' [15] [17] [19] u g
         where
          Q' : Brw → Type ℓ
          Q' u = (P ↔ limit f + ω ≤ u) → ordinal-dec (succ (limit f)) P
          i' : (u : Brw) → isProp (Q' u)
          i' u = isPropΠ (λ _ → isPropPropTrunc)

          [15] : Q' zero
          [15] h = ∣ (limit f {f↑} ,
                     (λ p → ⊥.rec (lim≰zero (lr h p))) ,
                     (λ l → ⊥.rec (<-irreflexive (limit f) l))) ∣

          [17] : {y : Brw} → Q' y → Q' (succ y)
          [17] {y} ih'' h = ∥-∥rec isPropPropTrunc ih'' ∣ [18] ∣
           where
            [18] : P ↔ (limit f + ω) ≤ y
            [18] = (λ p → lim≤sx→lim≤x _ y (lr h p)) , (λ l → rl h (≤-succ-incr l))

          [19] : {g : ℕ → Brw} {g↑ : increasing g}
               → ((k : ℕ) → Q' (g k)) → Q' (limit g {g↑})
          [19] {g} {g↑} ih'' h = ∣ limit g {g↑} , [20] , [21] ∣
           where
            [20] : P → succ (limit f) ≤ limit g
            [20] p = rl (limit-<-x↔limit+ω-≤-⇑-x f (limit g)) (lr h p)

            [21] : succ (limit f) ≤ limit g → P
            [21] l = rl h (lr (limit-<-x↔limit+ω-≤-⇑-x f (limit g)) l)

------------------------------------------------------------
-- The rounding down function ⇓ gives the greatest lower limit

⇓ : Brw → Brw
⇓ zero = zero
⇓ (succ x) = ⇓ x
⇓ (limit f {f↑}) = limit f {f↑}
⇓ (bisim f {f↑} g {g↑} x i) = bisim f {f↑} g {g↑} x i
⇓ (trunc x y p q i j) =  trunc (⇓ x) (⇓ y) (cong ⇓ p) (cong ⇓ q) i j

⇓-Islim⊎zero : (x : Brw) → Brw-zero-or-limit (⇓ x)
⇓-Islim⊎zero = Brw-ind P (λ x → isPropBrw-zero-or-limit (⇓ x)) P₀ (λ {s} → Pₛ s) Pₗ
 where
  P : (x : Brw) → Type
  P x = Brw-zero-or-limit (⇓ x)

  P₀ : P zero
  P₀  = inr refl

  Pₛ : (x : Brw) → P x → P (succ x)
  Pₛ x e = e

  Pₗ : {h : ℕ → Brw} {h↑ : increasing h} → ((k : ℕ) → P (h k)) → P (limit h {h↑})
  Pₗ {h} {h↑} z  = inl (is-lim-limit h h↑)

⇓ᶻˡ : Brw → Brwᶻˡ
⇓ᶻˡ x = (⇓ x , ⇓-Islim⊎zero x)

⇓x≤x : (x : Brw) → ⇓ x ≤ x
⇓x≤x  = Brw-ind P (λ x → ≤-trunc) P₀ Pₛ Pₗ
 where
  P : Brw → Type
  P x = ⇓ x ≤ x
  P₀ : P zero
  P₀  = ≤-zero
  Pₛ : {x : Brw} → P x → P (succ x)
  Pₛ e = ≤-trans e (<-in-≤ ≤-refl)
  Pₗ : {h : ℕ → Brw} {h↑ : increasing h} → ((k : ℕ) → P (h k)) → P (limit h {h↑})
  Pₗ {h} {h↑} z  = ≤-refl

⇓-right-≤ : (y : Brw) → Brw-zero-or-limit y → (x : Brw) → y ≤ x ↔ y ≤ ⇓ x
⇓-right-≤ y y-zl = Brw-ind _ (λ _ → isProp↔ ≤-trunc ≤-trunc) ↔-refl [1] λ _ → ↔-refl
 where
  [1] : {x : Brw} → y ≤ x ↔ y ≤ ⇓ x → y ≤ succ x ↔ y ≤ ⇓ x
  [1] {x} IH = [2] y-zl , (λ l → ≤-trans (rl IH l) ≤-succ-incr-simple)
   where
    [2] : is-lim y ⊎ (y ≡ zero) → y ≤ succ x → y ≤ ⇓ x
    [2] (inr y-zero) _ = subst (_≤ ⇓ x) (sym y-zero) ≤-zero
    [2] (inl y-lim ) l = lr IH (lem y y-lim l)
     where
      lem : (y : Brw) → is-lim y → y ≤ succ x → y ≤ x
      lem = reduce-to-canonical-limits _ (λ _ → isProp→ ≤-trunc)
                                       (λ f f↑ → lim≤sx→lim≤x f x)

⇓-finite-is-zero' : (n : ℕ) → ⇓ (ι n) ≡ zero
⇓-finite-is-zero' zero = refl
⇓-finite-is-zero' (suc n) = ⇓-finite-is-zero' n

⇓-finite-is-zero : (x : Brw) → isFinite x → ⇓ x ≡ zero
⇓-finite-is-zero x xisfin =
 ∥-∥rec (Brw-is-set (⇓ x) zero) [1] (fst (isFinite-correct x) xisfin)
  where
   [1] : Σ ℕ (λ n → ι n ≡ x) → ⇓ x ≡ zero
   [1] (n , e) = subst (λ - → ⇓ - ≡ zero) e (⇓-finite-is-zero' n)

nonzero-⇓-islim : (x : Brw) → (zero < ⇓ x) → is-lim (⇓ x)
nonzero-⇓-islim = Brw-ind P (λ x → isProp→ PropTrunc.isPropPropTrunc)
                              P₀ (λ {x} → Pₛ {x}) Pₗ
 where
  P : Brw → Type
  P x = zero < ⇓ x → is-lim (⇓ x)
  P₀ : P zero
  P₀ p = ⊥.elim (<-irreflexive zero p)
  Pₛ : {x : Brw} → P x → P (succ x)
  Pₛ e = e
  Pₗ : {h : ℕ → Brw} {h↑ : increasing h}
     → ((k : ℕ) → P (h k)) → P (limit h {h↑})
  Pₗ {h} {h↑} z  = λ p → is-lim-limit h h↑

finite-part : (x : Brw) → ℕ
finite-part  zero = 0
finite-part (succ x) = suc (finite-part x)
finite-part (limit f) = 0
finite-part (bisim f g x i) = 0
finite-part (trunc x y p q i j) =
 isSetℕ (finite-part x) (finite-part y)
        (cong finite-part p) (cong finite-part q) i j

decompose-⇓-fin : (x : Brw) → x ≡ (⇓ x) + ι (finite-part x)
decompose-⇓-fin = Brw-ind _ (λ x → Brw-is-set x _)
                      refl
                      (λ {x} r → cong succ r)
                      (λ _ → refl)

⇓-monotone : (x y : Brw) → y ≤ x → ⇓ y ≤ ⇓ x
⇓-monotone x y = Brw-ind P (λ x → isProp→ ≤-trunc) P₀ Pₛ Pₗ y
 where
  P : Brw → Type
  P y =  y ≤ x → ⇓ y ≤ ⇓ x

  P₀ : P zero
  P₀ = λ z → ≤-zero

  Pₛ : {y : Brw } → P y → P (succ y)
  Pₛ {y} p  = λ ps →  p (≤-trans ≤-succ-incr-simple ps)

  Pₗ :  {h : ℕ → Brw} {h↑ : increasing h} → ((k : ℕ) → P (h k)) → P (limit h {h↑})
  Pₗ {h} {h↑} hp = Brw-ind Q (λ x → isProp→ ≤-trunc) Q₀ Qₛ Qₗ x
   where
    Q : Brw → Type
    Q x =  (limit h) {h↑}  ≤ x → limit h {h↑} ≤ ⇓ x

    Q₀ : Q zero
    Q₀ z = z

    Qₛ : {x : Brw } → Q x → Q (succ x)
    Qₛ {x} p ps = p (lim≤sx→lim≤x h x ps)

    Qₗ :  {g : ℕ → Brw} {g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
    Qₗ hg z = z

lim≤x→lim≤⇓x : (x : Brw)
             → (f : ℕ → Brw) → {f↑ : increasing f}
             → (limit f {f↑} ≤ x
             → limit f {f↑} ≤ ⇓ x)
lim≤x→lim≤⇓x x f p = ⇓-monotone x (limit f) p

lim≤x↔lim≤⇓x : (x : Brw)
             → (f : ℕ → Brw) → {f↑ : increasing f}
             → (limit f {f↑} ≤ x
             ↔ limit f {f↑} ≤ ⇓ x)
lim≤x↔lim≤⇓x x f = lim≤x→lim≤⇓x x f , λ l → ≤-trans l (⇓x≤x x)

limf≤⇓fin→⊥ :(x : Brw) → (f : ℕ → Brw) → {f↑ : increasing f}
            → ⇓ x ≡ zero → limit f {f↑} ≤ x → ⊥
limf≤⇓fin→⊥ x f {f↑} p q =
 lim≰zero (subst (λ z → limit f {f↑} ≤ z ) p (lim≤x→lim≤⇓x x f q))

-- Partial Upward Closure Results

ω·k-dec→ω·k+1-dec : (P : Type ℓ) (k : ℕ)
                   → ordinal-dec (ω · (ι k)) P
                   → ordinal-dec (ω · (ι (suc k))) P
ω·k-dec→ω·k+1-dec P 0 d = ∥-∥map [1] d
 where
  [1] : ordinal-dec-str zero P  → ordinal-dec-str (zero + ω) P
  [1] (u , h) = (zero + ω , (λ _ → ≤-refl) , λ _ → rl h ≤-zero)
ω·k-dec→ω·k+1-dec P k@(suc k') = ∥-∥map [1]
 where
  [1] : ordinal-dec-str (ω · ι k) P → ordinal-dec-str (ω · succ (ι k)) P
  [1] (x , impl₁ , impl₂) = x + ω , [2] , [3]
   where
    [2] : P → ω · ι k + ω ≤ x + ω
    [2] p = +x-mono ω (impl₁ p)
    [3] : ω · ι k + ω ≤ x + ω → P
    [3] l = impl₂ (lim-cancel-+ω-≤ x (ω · ι k) (ω·sk-islim k') l)

ωᵏ-dec→ωᵏ⁺¹-dec : (P : Type ℓ) (k : ℕ)
               → ordinal-dec (ω ^ (ι k)) P
               → ordinal-dec (ω ^ (ι (suc k))) P
ωᵏ-dec→ωᵏ⁺¹-dec P k = ∥-∥map [1]
 where
  [1] : ordinal-dec-str (ω ^ ι k) P → ordinal-dec-str (ω ^ succ (ι k)) P
  [1] (x , impl₁ , impl₂) = ω · x , [2] , [3]
   where
    [2] : P → ω ^ ι k · ω ≤ ω · x
    [2] p = subst (_≤ ω · x) (sym (ω-finite-power-comm k)) (x·-mono (impl₁ p))
    [3] : ω ^ ι k · ω ≤ ω · x → P
    [3] l = impl₂ (ω·-cancel-≤ (ω ^ ι k) x (subst (_≤ ω · x) (ω-finite-power-comm k) l))

ω·-sequence : (ℕ → ℕ) → ℕ → Brw
ω·-sequence t k = ω · ι (t k) + ι k

ω·-sequence-increasing : (t : ℕ → ℕ)
                       → ((n : ℕ) → t n N.≤ t (suc n))
                       → increasing (ω·-sequence t)
ω·-sequence-increasing t t-incr k = ≤∘<-in-< [1] [2]
 where
  [1] : ω · ι (t k) + ι k ≤ ω · ι (t (suc k)) + ι k
  [1] = +x-mono (ι k) (x·-mono (ι-mono (t-incr k)))
  [2] : ω · ι (t (suc k)) + ι k < ω·-sequence t (suc k)
  [2] = x+-mono-< {ω · ι (t (suc k))} {ι k} ≤-refl

limit-of-ω·-sequence-≤
 : (t s : ℕ → ℕ)
   (t-incr : (n : ℕ) → t n N.≤ t (suc n))
   (s-incr : (n : ℕ) → s n N.≤ s (suc n))
 → ((n : ℕ) → s n N.≤ t n N+ 1)
 → limit (ω·-sequence s) {ω·-sequence-increasing s s-incr}
 ≤ limit (ω·-sequence t) {ω·-sequence-increasing t t-incr} + ω
limit-of-ω·-sequence-≤ t s t-incr s-incr s≤t =
 weakly-bisimilar→lim≤lim (ω·-sequence s)
                          (λ n → limit (ω·-sequence t) + ι n)
                          [1]
  where
   [1] : ω·-sequence s ≲ (λ n → limit (ω·-sequence t) + ι n)
   [1] k = ∣ (k , +x-mono (ι k) [2]) ∣
    where
     e = cong (λ - → ω · ι -) (+-comm (t k) 1)
     [2] = ω · ι (s k)           ≤⟨ x·-mono (ι-mono (s≤t k)) ⟩
           ω · ι (t k N+ 1)      ≤⟨ ≤-refl-≡ e ⟩
           ω · ι (t k) + ω       ≤⟨ simulation→≤ [3] ⟩
           limit (ω·-sequence t) ≤∎
      where
       [3] : (n : ℕ) → Σ ℕ (λ m → ω · ι (t k) + ι n ≤ ω·-sequence t m)
       [3] n = (n N+ k , [4])
        where
         t-mono : (u v : ℕ) → t v N.≤ t (u N+ v)
         t-mono zero v = N.≤-refl
         t-mono (suc u) v = N.≤-trans (t-mono u v) (t-incr (u N+ v))
         [4] : ω · ι (t k) + ι n ≤ ω · ι (t (n N+ k)) + ι (n N+ k)
         [4] = +-mono {ω · ι (t k)} {ι n} {ω · ι (t (n N+ k))} {ι (n N+ k)}
                (x·-mono (ι-mono (t-mono n k)))
                (ι-mono N.≤SumLeft)
