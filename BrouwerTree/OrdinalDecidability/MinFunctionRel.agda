{-# OPTIONS --cubical --erasure --guardedness #-}
module BrouwerTree.OrdinalDecidability.MinFunctionRel where

open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _N+_)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary

open import Iff
open import PropTrunc

open import BrouwerTree.Everything

open import  BrouwerTree.OrdinalDecidability.Basic
open import  BrouwerTree.OrdinalDecidability.GeneralProperties


-- Definition of relational limMin simultaneously with its monotonicity

mutual
 data limMin[_,_]~_ : Brw → Brw → Brw → Type where
  zero-left : (y : Brw) → limMin[ zero , y ]~ zero
  succ-left : (x y z : Brw) → limMin[ x , y ]~ z → limMin[ succ x , y ]~ z
  lim-zero : (f : ℕ → Brw) {f↑ : increasing f} → limMin[ limit f {f↑} , zero ]~ zero
  lim-succ : (f : ℕ → Brw) {f↑ : increasing f} (y z : Brw)
           → limMin[ limit f {f↑} , y ]~ z → limMin[ limit f {f↑} , succ y ]~ z
  lim-lim : (f g : ℕ → Brw) {f↑ : increasing f} {g↑ : increasing g}
          → (r : ℕ → Brw)
          → (rspec : (n : ℕ) → limMin[ f n , g n ]~ r n)
          → let r↑ = λ n → ≤-succ-mono (+x-mono (ι n)
                                                (limMin[,]~-mono (<-in-≤ (f↑ n))
                                                                 (<-in-≤ (g↑ n))
                                                                 (rspec n)
                                                                 (rspec (suc n))))
          in limMin[ limit f {f↑} , limit g {g↑} ]~ limit (λ n → r n + ι n) {r↑}
  trunc : {x y z : Brw} → (p q : limMin[ x , y ]~ z) → p ≡ q

 limMin[,]~-mono : {x x' y y' z z' : Brw} → x ≤ x' → y ≤ y'
                 → limMin[ x , y ]~ z → limMin[ x' , y' ]~ z' → z ≤ z'
 limMin[,]~-mono u v (zero-left y) σ = ≤-zero
 limMin[,]~-mono u v (succ-left x₁ y z ρ) σ =
  limMin[,]~-mono (≤-trans ≤-succ-incr-simple u) v ρ σ
 limMin[,]~-mono u v (lim-zero f) σ = ≤-zero
 limMin[,]~-mono u v (lim-succ f y₁ z ρ) σ =
  limMin[,]~-mono  u (≤-trans ≤-succ-incr-simple v) ρ σ
 limMin[,]~-mono u v (lim-lim f g r rspec) (zero-left y') = ⊥.rec (lim≰zero u)
 limMin[,]~-mono u v (lim-lim f g r rspec) (succ-left x₁ y' z' σ) =
  limMin[,]~-mono  (lim≤sx→lim≤x f x₁ u) v (lim-lim f g r rspec) σ
 limMin[,]~-mono u v (lim-lim f g r rspec) (lim-zero f₁) = ⊥.rec (lim≰zero v)
 limMin[,]~-mono u v (lim-lim f g r rspec) (lim-succ f₁ y₁ z' σ) =
  limMin[,]~-mono u (lim≤sx→lim≤x g y₁ v) (lim-lim f g r rspec) σ
 limMin[,]~-mono u v (lim-lim f f' {f↑} {f'↑} r rspec) (lim-lim g g' {g↑} {g'↑} s sspec) =
  weakly-bisimilar→lim≤lim _ _ h
   where
     h : (λ k → r k + ι k) ≲ (λ k → s k + ι k)
     h k  =  ∥-∥rec isPropPropTrunc β (lim≤lim→weakly-bisimilar f g u k)
      where
       β :  Σ[ n ∈ ℕ ] f k ≤ g n → ∃[ n ∈ ℕ ] (r k + ι k ≤ s n + ι n)
       β (n₁ , m₁) = ∥-∥map α (lim≤lim→weakly-bisimilar f' g' v k)
        where
         α : Σ[ n ∈ ℕ ] f' k ≤ g' n → Σ[ n ∈ ℕ ] r k + ι k ≤ s n + ι n
         α (n₂ , m₂) = (n₀ , u₀)
          where
           n₀ = n₁ N+ (n₂ N+ k)
           u₀ : r k + ι k ≤ s n₀ + ι n₀
           u₀ = +-mono w (ι-mono (N.≤-trans (N.≤SumRight {k}) (N.≤SumRight {k = n₁})))
            where
             w : r k ≤ s n₀
             w = limMin[,]~-mono u₁ u₂ (rspec k) (sspec n₀)
              where
               u₁ : f k ≤ g n₀
               u₁ = ≤-trans m₁ (increasing-monotone g↑ (N.≤SumLeft {n₁}))

               u₂ : f' k ≤ g' n₀
               u₂ = ≤-trans m₂
                            (increasing-monotone g'↑ (N.≤-trans (N.≤SumLeft {n₂})
                                                                (N.≤SumRight {k = n₁})))
 limMin[,]~-mono u v (lim-lim f g r rspec) (trunc σ σ' i) =
  isProp→PathP (λ i → ≤-trunc) (limMin[,]~-mono  u v (lim-lim f g r rspec) σ)
                               (limMin[,]~-mono u v (lim-lim f g r rspec) σ') i
 limMin[,]~-mono u v (trunc ρ ρ' i) σ =
  isProp→PathP (λ i → ≤-trunc) (limMin[,]~-mono u v ρ σ)
                               (limMin[,]~-mono u v ρ' σ) i


limMin[,]~-single-valued : {x y z z' : Brw}
                         → limMin[ x , y ]~ z → limMin[ x , y ]~ z' → z ≡ z'
limMin[,]~-single-valued ρ σ =
 ≤-antisym (limMin[,]~-mono ≤-refl ≤-refl ρ σ) (limMin[,]~-mono  ≤-refl ≤-refl σ ρ)

limMin[,]-outputs-unique : {x y : Brw} → isProp (Σ[ z ∈ Brw ] limMin[ x , y ]~ z)
limMin[,]-outputs-unique (z , r) (z' , r') =
 Σ≡Prop (λ w → trunc) (limMin[,]~-single-valued r r')

limMin[,]~-total : (x y : Brw) → Σ[ z ∈ Brw ] limMin[ x , y ]~ z
limMin[,]~-total = Brw-ind P (λ x → isPropΠ (λ y → limMin[,]-outputs-unique)) P₀ Pₛ Pₗ
 where
  P : Brw → Type
  P x = (y : Brw) →  Σ[ z ∈ Brw ] limMin[ x , y ]~ z
  P₀ : P zero
  P₀ y = zero , zero-left y
  Pₛ : {x : Brw} → P x → P (succ x)
  Pₛ {x} p y = (fst (p y)) , (succ-left x y (fst (p y)) (snd (p y)))
  Pₗ : {f : ℕ → Brw} {f↑ : increasing f}
    → ((k : ℕ) → P (f k)) → P (limit f {f↑})
  Pₗ {f} {f↑} p = Brw-ind Q (λ x → limMin[,]-outputs-unique) (zero , lim-zero f) Qₛ Qₗ
   where
    Q : Brw → Type
    Q y = Σ[ z ∈ Brw ] limMin[ limit f , y ]~ z
    Qₛ : {y : Brw} → Q y → Q (succ y)
    Qₛ {y} q = (fst q) , (lim-succ f y (fst q) (snd q))
    Qₗ : {g : ℕ → Brw} {g↑ : increasing g}
       → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
    Qₗ {g} {g↑} q = (limit (λ n → r n + ι n)) , (lim-lim f g r rspec)
     where
      r : ℕ → Brw
      r n = fst (p n (g n))
      rspec : (n : ℕ) → limMin[ f n , g n ]~ r n
      rspec n = snd (p n (g n))
      r↑ : increasing (λ n → r n + ι n)
      r↑ n = ≤-succ-mono (+x-mono (ι n) (limMin[,]~-mono
                         (<-in-≤ (f↑ n)) (<-in-≤ (g↑ n)) (rspec n) (rspec (suc n))))



-------------------- Definition and monotonicity of limMin as a function: --------------

limMin : Brw → Brw → Brw
limMin x y = fst (limMin[,]~-total x y)

limMin-spec : (x y : Brw) → limMin[ x , y ]~ (limMin x y)
limMin-spec x y = snd (limMin[,]~-total x y)

limMin-mono : {x x' y y' : Brw} → x ≤ x' → y ≤ y' → limMin x y ≤ limMin x' y'
limMin-mono {x} {x'} {y} {y'} u v =
 limMin[,]~-mono u v (limMin-spec x y) (limMin-spec x' y')

private
 limMin-zero-y≡zero : (y : Brw) → limMin zero y ≡ zero
 limMin-zero-y≡zero y = refl

 limMin-succ⟨x⟩-y≡limMin-x-y : (x y : Brw) → limMin (succ x) y ≡ limMin x y
 limMin-succ⟨x⟩-y≡limMin-x-y x y = refl

 limMin-limit⟨f⟩-limit⟨g⟩≡limit⟨limMin-fn-gn+n⟩
  : (f g : ℕ → Brw) {f↑ : increasing f} {g↑ : increasing g}
  → limMin (limit f {f↑}) (limit g {g↑})
     ≡ limit (λ n → limMin (f n) (g n) + ι n)
             {λ n → ≤-succ-mono (+x-mono (ι n)
                                         (limMin-mono (<-in-≤ (f↑ n)) (<-in-≤ (g↑ n))))}
 limMin-limit⟨f⟩-limit⟨g⟩≡limit⟨limMin-fn-gn+n⟩ f g {f↑} {g↑} = refl

-------------------- Properties of limMin --------------------------

limMin-left : (x y : Brw) → limMin x y ≤ x
limMin-left =
 Brw-ind (λ x → (y : Brw) → limMin x y ≤ x) (λ x → isPropΠ (λ y → ≤-trunc)) P₀ Pₛ Pₗ
  where
   P₀ : (y : Brw) → limMin zero y ≤ zero
   P₀ y = ≤-refl

   Pₛ : {x : Brw}
      → ((y : Brw) → limMin x y ≤ x)
      → (y : Brw) → limMin (succ x) y ≤ succ x
   Pₛ {x} r y = ≤-trans (r y) ≤-succ-incr-simple

   Pₗ : {f : ℕ → Brw} {f↑ : increasing f}
      → ((k : ℕ) (y : Brw) → limMin (f k) y ≤ f k)
      → (y : Brw) → limMin (limit f {f↑}) y ≤ limit f {f↑}
   Pₗ {f} {f↑} r =
    Brw-ind (λ y → limMin (limit f) y ≤ limit f) (λ y → ≤-trunc) ≤-zero (λ u → u) h
     where
      h : {g : ℕ → Brw} {g↑ : increasing g}
        → ((k : ℕ) → limMin (limit f {f↑}) (g k) ≤ limit f {f↑})
        → limMin (limit f {f↑}) (limit g {g↑}) ≤ limit f {f↑}
      h {g} {g↑} r' = ≤-limiting (λ n → limMin (f n) (g n) + ι n) u
       where
        u : (k : ℕ) → limMin (f k) (g k) + ι k ≤ limit f {f↑}
        u k = ≤-trans (+x-mono (ι k) u₁) u₂
         where
          u₁ : limMin (f k) (g k) ≤ f k
          u₁ = r k (g k)
          u₂ : f k + ι k ≤ limit f {f↑}
          u₂ = add-finite-part-lemma f k

limMin-right : (x y : Brw) → limMin x y ≤ y
limMin-right = Brw-ind _ (λ x → isPropΠ (λ y → ≤-trunc)) (λ y → ≤-zero) (λ r → r) h
 where
  h : {f : ℕ → Brw} {f↑ : increasing f}
    → ((k : ℕ) (y : Brw) → limMin (f k) y ≤ y)
    → (y : Brw) → limMin (limit f {f↑}) y ≤ y
  h {f} {f↑} r = Brw-ind _ (λ y → ≤-trunc) ≤-refl (λ {x} r → ≤-trans r ≤-succ-incr-simple) u
   where
    u : {g : ℕ → Brw} {g↑ : increasing g}
      → ((k : ℕ) → limMin (limit f {f↑}) (g k) ≤ g k)
      → limMin (limit f {f↑}) (limit g {g↑}) ≤ limit g {g↑}
    u {g} {g↑} r' =
     ≤-limiting (λ n → limMin (f n) (g n) + ι n)
                (λ n → ≤-trans (+x-mono (ι n) (r n (g n))) (add-finite-part-lemma g n))

limMin-succ : (x y : Brw) → limMin x (succ y) ≡ limMin x y
limMin-succ = Brw-ind _ (λ x → isPropΠ (λ y → Brw-is-set _ _))
                        (λ y → refl) (λ {x} r y → r y) (λ {f} {f↑} r y → refl)

limMin-diagonal-is-⇓ : (x : Brw) → limMin x x ≡ ⇓ x
limMin-diagonal-is-⇓ = Brw-ind _ (λ x → Brw-is-set _ _)
                                 refl
                                 (λ {x} u → limMin-succ x x ∙ u)
                                 h
 where
  h : {f : ℕ → Brw} {f↑ : increasing f}
    → ((k : ℕ) → limMin (f k) (f k) ≡ ⇓ (f k))
    → limMin (limit f {f↑}) (limit f {f↑}) ≡ limit f {f↑}
  h {f} {f↑} r = ≤-antisym (limMin-left (limit f) (limit f)) (≤-limiting f u)
   where
    u : (k : ℕ) → f k ≤ limMin (limit f) (limit f)
    u k = ≤-cocone (λ n → limMin (f n) (f n) + ι n) {k = m} v
     where
      k₀ : ℕ
      k₀ = finite-part (f k)
      m : ℕ
      m = k N+ k₀
      v : f k ≤ (limMin (f m) (f m) + ι m)
      v = ≤-trans (≤-refl-≡ (decompose-⇓-fin (f k)))
                  (≤-trans (≤-refl-≡ (cong (_+ ι k₀) (sym (r k)))) w)
       where
        w : limMin (f k) (f k) + ι k₀ ≤ limMin (f m) (f m) + ι m
        w = ≤-trans (x+-mono w₁) (+x-mono (ι m) w₂)
         where
          w₁ : ι k₀ ≤ ι m
          w₁ = transport (cong (ι k₀ ≤_) (sym (ι-+-commutes k₀ k)))
                         (x+-increasing (ι k))
          w₂ : limMin (f k) (f k) ≤ limMin (f m) (f m)
          w₂ = limMin-mono (increasing-monotone f↑ N.≤SumLeft)
                           (increasing-monotone f↑ N.≤SumLeft)


limMin-diagonal-limit : (f : ℕ → Brw) {f↑ : increasing f}
                      → limMin (limit f) (limit f) ≡ limit f {f↑}
limMin-diagonal-limit f {f↑} = limMin-diagonal-is-⇓ (limit f)


----- Theorem : Ordinal Decidability is Closed Under Binary Conjunction --------

limMin-key-property-str : (f : ℕ → Brw) {f↑ : increasing f} (x y : Brw)
                        → limit f {f↑} ≤ x
                        → limit f {f↑} ≤ y
                        → limit f {f↑} ≤ limMin x y
limMin-key-property-str f x y u v =
 transport (cong (_≤ limMin x y) (limMin-diagonal-limit f)) (limMin-mono u v)

limMin-key-property : (α : Brw) → is-lim α → (x y : Brw)
                    → α ≤ x
                    → α ≤ y
                    → α ≤ limMin x y
limMin-key-property α αIsLim x y = ∥-∥rec (isProp→ (isProp→ ≤-trunc)) H αIsLim
 where
  H : is-Σlim α → α ≤ x → α ≤ y → α ≤ limMin x y
  H ((f , f↑) , (p₀ , p₁)) α≤x α≤y =
   transport (cong (_≤ limMin x y)  limf=α)
             (limMin-key-property-str f x y limf≤x limf≤y)
   where
    limf=α : limit f {f↑} ≡ α
    limf=α = ≤-antisym (≤-limiting f p₀) (p₁ (limit f) λ i → ≤-cocone-simple f)
    limf≤x : limit f ≤ x
    limf≤x = transport (cong (_≤ x) (sym limf=α)) α≤x
    limf≤y : limit f ≤ y
    limf≤y =  transport (cong (_≤ y) (sym limf=α)) α≤y

ordinal-dec-×-aux : {ℓ : Level} (P Q : Type ℓ) (α : Brw) → is-lim α
                  → ordinal-dec α P
                  → ordinal-dec α Q
                  → ordinal-dec α (P × Q)
ordinal-dec-×-aux P Q α α-lim = ∥-∥map2 h
 where
  h : ordinal-dec-str α P → ordinal-dec-str α Q → ordinal-dec-str α (P × Q)
  h (x , e₁) (y , e₂) =
   limMin x y ,
   (λ (p , q) → limMin-key-property α α-lim x y (lr e₁ p) (lr e₂ q)) ,
   (λ l → rl e₁ (≤-trans l (limMin-left x y)) ,
          rl e₂ (≤-trans l (limMin-right x y)))

ordinal-dec-× : {ℓ : Level} (P Q : Type ℓ) → isProp P → isProp Q
              → (α : Brw)
              → ordinal-dec α P
              → ordinal-dec α Q
              → ordinal-dec α (P × Q)
ordinal-dec-× P Q PProp QProp α hP hQ with dec-n≡ α 0
... | yes α-zero =
 subst (λ - → ordinal-dec - (P × Q)) α-zero
       (rl (zero-decidable-iff-true (P × Q) (isProp× PProp QProp))
         (lr (zero-decidable-iff-true P PProp)
             (subst (λ - → ordinal-dec - P) (sym α-zero) hP) ,
         (lr (zero-decidable-iff-true Q QProp)
             (subst (λ - → ordinal-dec - Q) (sym α-zero) hQ))))
... | no α-non-zero =
 rl (ordinal-dec-equivalent-lim-benchmark (P × Q) (isProp× PProp QProp) α) [3]
  where
   [1] : ordinal-dec (⇑ α) P
   [1] = lr (ordinal-dec-equivalent-lim-benchmark P PProp α) hP
   [2] : ordinal-dec (⇑ α) Q
   [2] = lr (ordinal-dec-equivalent-lim-benchmark Q QProp α) hQ
   [3] : ordinal-dec (⇑ α) (P × Q)
   [3] = ordinal-dec-×-aux P Q (⇑ α) [4] [1] [2]
    where
     [4] : is-lim (⇑ α)
     [4] with (⇑-is-lim α)
     ... | inl α-lim = α-lim
     ... | inr α-zero = ⊥.elim (α-non-zero (sym α-zero))

-------------------------------------------------------
----------Definition of limMin over Brwᶻˡ---------------

limMin-is-zl : (x y : Brw) → Brw-zero-or-limit (limMin x y)
limMin-is-zl =
 Brw-ind P (λ z → isPropΠ (λ x → isPropBrw-zero-or-limit _)) P₀ (λ {s} → Pₛ s) Pₗ
 where
  P : Brw → Type
  P x = (y : Brw) → Brw-zero-or-limit (limMin x y)

  P₀ : P zero
  P₀ y = inr refl

  Pₛ : (x : Brw) → P x → P (succ x)
  Pₛ x p y = p y

  Pₗ : {f : ℕ → Brw} {f↑ : increasing f} → ((k : ℕ) → P (f k)) → P (limit f {f↑})
  Pₗ {f} {f↑} p = Brw-ind Q (λ y → isPropBrw-zero-or-limit _) Q₀ (λ {s} → Qₛ s) Qₗ
   where
    Q : Brw → Type
    Q y =  Brw-zero-or-limit (limMin (limit f) y)

    Q₀ : Q zero
    Q₀ = inr refl

    Qₛ : (y : Brw) → Q y → Q (succ y)
    Qₛ y q = q

    Qₗ : {g : ℕ → Brw} {g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g)
    Qₗ {g} {g↑} q =
     inl ∣ ((λ n → r n + ι n) , r↑) , limit-is-sup (λ z → r z + ι z) r↑ ∣
      where
       r : ℕ → Brw
       r n = limMin (f n) (g n)
       rspec : (n : ℕ) → limMin[ f n , g n ]~ r n
       rspec n = limMin-spec (f n) (g n)
       r↑ : increasing (λ n → r n + ι n)
       r↑ n = ≤-succ-mono (+x-mono (ι n)
                                   (limMin-mono (<-in-≤ (f↑ n)) (<-in-≤ (g↑ n))))

limMinᶻˡ : Brwᶻˡ →  Brwᶻˡ →  Brwᶻˡ
limMinᶻˡ (x , hx) (y , hy) = (limMin x y , limMin-is-zl x y)
