{-# OPTIONS --cubical --erasure --guardedness #-}
module BrouwerTree.OrdinalDecidability.MaxFunctionRel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _N+_)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Iff
open import PropTrunc

open import BrouwerTree.Everything

open import  BrouwerTree.OrdinalDecidability.Basic
open import  BrouwerTree.OrdinalDecidability.GeneralProperties

-- Definition of relational limMax simultaneously with (1) its
-- monotonicity and (2) a compatibility with ⇓

mutual
 data limMax[_,_]~_ : Brw → Brw → Brw → Type where
  zero-zero : limMax[ zero , zero ]~ zero
  zero-succ : {y z : Brw} → limMax[ zero , y ]~ z → limMax[ zero , succ y ]~ z
  zero-lim : {f : ℕ → Brw}{f↑ : increasing f}
           → (t : ℕ → Brw) → ((n : ℕ) → limMax[ zero , f n ]~ t n)
           → limMax[ zero , limit f {f↑} ]~ (limit f {f↑})
  succ-zero : {x z : Brw} → limMax[ x , zero ]~ z → limMax[ succ x , zero ]~ z
  succ-succ : {x y z : Brw} → limMax[ x , y ]~ z → limMax[ succ x , succ y ]~ z
  succ-lim : {x z : Brw}{f : ℕ → Brw}{f↑ : increasing f}
           → limMax[ x , limit f {f↑} ]~ z → limMax[ succ x , limit f {f↑} ]~ z
  lim-zero : {f : ℕ → Brw}{f↑ : increasing f}
           → (l : ℕ → Brw) → ((n : ℕ) → limMax[ f n , zero ]~ l n)
           → limMax[ limit f {f↑} , zero ]~ (limit f {f↑})
  lim-succ : {f : ℕ → Brw}{f↑ : increasing f}{y z : Brw}
           → limMax[ limit f {f↑} , y ]~ z → limMax[ limit f {f↑} , succ y ]~ z
  lim-lim : {f g : ℕ → Brw}{f↑ : increasing f}{g↑ : increasing g}
          → (r : ℕ → Brw) → (rspec : (n : ℕ) → limMax[ f n , g n ]~ r n)
          → let r+ι↑ = λ n → ≤-succ-mono
                             (+x-mono (ι n)
                                      (limMax[,]~-mono (<-in-≤ (f↑ n))
                                                       (<-in-≤ (g↑ n))
                                                       (rspec n)
                                                       (rspec (suc n))))
          in limMax[ limit f {f↑} , limit g {g↑} ]~ limit (λ n → r n + ι n) {r+ι↑}
  trunc : {x y z : Brw} → (p q : limMax[ x , y ]~ z) → p ≡ q

 limMax[,]~-mono : {x x' y y' z z' : Brw}
                 → x ≤ x'
                 → y ≤ y'
                 → limMax[ x , y ]~ z
                 → limMax[ x' , y' ]~ z'
                 → z ≤ z'
 limMax[,]~-mono u v zero-zero q = ≤-zero
 limMax[,]~-mono u v (zero-succ p) q =
  limMax[,]~-mono u (≤-trans ≤-succ-incr-simple v) p q
 limMax[,]~-mono u v (zero-lim t tspec) zero-zero = v
 limMax[,]~-mono u v p@(zero-lim t tspec) (zero-succ q) =
  limMax[,]~-mono u (lim≤sx→lim≤x _ _ v) p q
 limMax[,]~-mono u v (zero-lim t tspec) (zero-lim t' tspec') = v
 limMax[,]~-mono u v (zero-lim t tspec) (succ-zero q) = ≤-trans v ≤-zero
 limMax[,]~-mono u v p@(zero-lim t tspec) (succ-succ q) =
  limMax[,]~-mono ≤-zero (lim≤sx→lim≤x _ _ v ) p q
 limMax[,]~-mono u v p@(zero-lim t tspec) (succ-lim q) =
  limMax[,]~-mono ≤-zero v p q
 limMax[,]~-mono u v (zero-lim t tspec) (lim-zero l lspec) = ≤-trans v u
 limMax[,]~-mono u v p@(zero-lim t tspec) (lim-succ q) =
  limMax[,]~-mono u (lim≤sx→lim≤x _ _ v) p q
 limMax[,]~-mono u v (zero-lim {f} t tspec) (lim-lim {g} {g'} {g↑} {g'↑} r rspec) =
  weakly-bisimilar→lim≤lim f (λ k → r k + ι k) h
   where
    h : f ≲ (λ k → r k + ι k)
    h k = ∥-∥map β (lim≤lim→weakly-bisimilar f g' v k)
     where
      β :  Σ[ n ∈ ℕ ] f k ≤ g' n → Σ[ m ∈ ℕ ] f k ≤ r m + ι m
      β (n , p) = m , p'
       where
        m₁ : ℕ
        m₁ = finite-part (f k)
        m : ℕ
        m = n N+ m₁
        p' = f k        ≤⟨ subst (_≤ r m + ι m₁) [1] [2] ⟩
             r m + ι m₁ ≤⟨ [3] ⟩
             r m + ι m  ≤∎
         where
          [1] : t k + ι m₁ ≡ f k
          [1] = cong (_+ ι m₁) (zero-max-unique ≤-zero (tspec k)) ∙
                sym (decompose-⇓-fin (f k))
          [2] : t k + ι m₁ ≤ r m + ι m₁
          [2] = +x-mono (ι m₁) (≤-trans [2]₁ [2]₂)
           where
            [2]₁ : t k ≤ r n
            [2]₁ = limMax[,]~-mono ≤-zero p (tspec k) (rspec n)
            [2]₂ : r n ≤ r m
            [2]₂ = limMax[,]~-mono (increasing-monotone g↑ N.≤SumLeft)
                                   (increasing-monotone g'↑ N.≤SumLeft)
                                   (rspec n)
                                   (rspec m)
          [3] : r m + ι m₁ ≤ r m + ι m
          [3] = x+-mono (increasing-monotone ι-increasing (N.≤SumRight {m₁} {n}))
 limMax[,]~-mono u v (zero-lim t tspec) (trunc q q₁ i) =
  isProp→PathP (λ i → ≤-trunc) (limMax[,]~-mono u v (zero-lim t tspec) q)
                               (limMax[,]~-mono u v (zero-lim t tspec) q₁) i
 limMax[,]~-mono u v (succ-zero p) q =
  limMax[,]~-mono (≤-trans ≤-succ-incr-simple u)  v p q
 limMax[,]~-mono u v (succ-succ p) q =
  limMax[,]~-mono (≤-trans ≤-succ-incr-simple  u) (≤-trans ≤-succ-incr-simple v) p q
 limMax[,]~-mono u v (succ-lim p) q =
  limMax[,]~-mono (≤-trans ≤-succ-incr-simple u) v p q
 limMax[,]~-mono u v (lim-zero l lspec) zero-zero = u
 limMax[,]~-mono u v (lim-zero l lspec) (zero-succ q) = ≤-trans u ≤-zero
 limMax[,]~-mono u v (lim-zero l lspec) (zero-lim t tspec) = ≤-trans u v
 limMax[,]~-mono u v (lim-zero l lspec) (succ-zero q) =
  limMax[,]~-mono (lim≤sx→lim≤x _ _ u) v (lim-zero l lspec) q
 limMax[,]~-mono u v (lim-zero l lspec) (succ-succ q) =
  limMax[,]~-mono (lim≤sx→lim≤x _ _ u) ≤-zero (lim-zero l lspec) q
 limMax[,]~-mono u v (lim-zero l lspec) (succ-lim q) =
  limMax[,]~-mono (lim≤sx→lim≤x _ _ u) v (lim-zero l lspec) q
 limMax[,]~-mono u v (lim-zero l lspec) (lim-zero l' lspec') = u
 limMax[,]~-mono u v (lim-zero l lspec) (lim-succ q) =
  limMax[,]~-mono u ≤-zero (lim-zero l lspec) q
 limMax[,]~-mono u v (lim-succ p) q =
  limMax[,]~-mono u (≤-trans ≤-succ-incr-simple v) p q
 limMax[,]~-mono u v (lim-zero {f} l lspec) (lim-lim {g} {g'} {g↑} {g'↑} r rspec) =
  weakly-bisimilar→lim≤lim f (λ k → r k + ι k) h
   where
    h : f ≲ (λ k → r k + ι k)
    h k  =  ∥-∥map β (lim≤lim→weakly-bisimilar f g u k)
     where
      β : Σ[ n ∈ ℕ ] f k ≤ g n → Σ[ m ∈ ℕ ] f k ≤ r m + ι m
      β (n , p) = m , p'
       where
        m₁ : ℕ
        m₁ = finite-part (f k)
        m : ℕ
        m = n N+ m₁
        p' = f k        ≤⟨ subst (_≤ r m + ι m₁) [1] [2] ⟩
             r m + ι m₁ ≤⟨ [3] ⟩
             r m + ι m  ≤∎
         where
            [1] : l k + ι (m₁) ≡ f k
            [1] = cong (_+ ι m₁) (max-zero-unique ≤-zero (lspec k)) ∙
                  sym (decompose-⇓-fin (f k))
            [2] : l k + ι m₁ ≤ r m + ι m₁
            [2] = +x-mono (ι m₁) (≤-trans [2]₁ [2]₂)
             where
              [2]₁ : l k ≤ r n
              [2]₁ = limMax[,]~-mono p ≤-zero (lspec k) (rspec n)
              [2]₂ : r n ≤ r m
              [2]₂ = limMax[,]~-mono (increasing-monotone g↑ N.≤SumLeft)
                                     (increasing-monotone g'↑ N.≤SumLeft)
                                     (rspec n)
                                     (rspec m)
            [3] : r m + ι m₁ ≤ r m + ι m
            [3] = x+-mono (increasing-monotone ι-increasing (N.≤SumRight {m₁} {n}))

 limMax[,]~-mono u v (lim-zero l lspec) (trunc p q i) =
  isProp→PathP (λ i → ≤-trunc) (limMax[,]~-mono u v (lim-zero l lspec) p)
                               (limMax[,]~-mono u v (lim-zero l lspec) q) i
 limMax[,]~-mono u v (lim-lim r rspec) zero-zero = ⊥.rec  (lim≰zero u)
 limMax[,]~-mono u v p@(lim-lim r rspec) (zero-succ q) =
  limMax[,]~-mono u (lim≤sx→lim≤x _ _ v) p q
 limMax[,]~-mono u v (lim-lim r rspec) (zero-lim t tspec) = ⊥.rec (lim≰zero u)
 limMax[,]~-mono u v (lim-lim r rspec) (succ-zero q) = ⊥.rec (lim≰zero v)
 limMax[,]~-mono u v p@(lim-lim r rspec) (succ-succ q) =
  limMax[,]~-mono (lim≤sx→lim≤x _ _ u) (lim≤sx→lim≤x _ _ v) p q
 limMax[,]~-mono u v p@(lim-lim r rspec) (succ-lim q) =
  limMax[,]~-mono (lim≤sx→lim≤x _ _ u) v p q
 limMax[,]~-mono u v (lim-lim r rspec) (lim-zero l lspec) = ⊥.rec (lim≰zero v)
 limMax[,]~-mono u v p@(lim-lim r rspec) (lim-succ q) =
  limMax[,]~-mono u (lim≤sx→lim≤x _ _ v) p q
 limMax[,]~-mono u v (lim-lim {f} {f'} {f↑} {f'↑} t tspec) (lim-lim {g} {g'} {g↑} {g'↑} r rspec) =
  weakly-bisimilar→lim≤lim (λ k → t k + ι k) (λ k → r k + ι k) h
   where
     h : (λ k → t k + ι k) ≲ (λ k → r k + ι k)
     h k = ∥-∥rec isPropPropTrunc β (lim≤lim→weakly-bisimilar f g u k)
      where
        β :  Σ[ n ∈ ℕ ] f k ≤ g n → ∃[ m ∈ ℕ ] t k + ι k ≤ r m + ι m
        β (n , p) = ∥-∥map α (lim≤lim→weakly-bisimilar f' g' v k)
         where
          α :  Σ[ n ∈ ℕ ] f' k ≤ g' n → Σ[ m ∈ ℕ ] t k + ι k ≤ r m + ι m
          α (n₁ , p₁) = m , p'
           where
            m = n N+ ( n₁ N+ k)
            p' : t k + ι k ≤ r m + ι m
            p' = +-mono (limMax[,]~-mono [1] [2] (tspec k) (rspec m))
                        (ι-mono (N.≤-trans (N.≤SumRight {k} {n₁})
                                           (N.≤SumRight {n₁ N+ k}{n})))
             where
              [0] : n₁ N.≤ n N+ (n₁ N+ k)
              [0] = N.≤-trans (N.≤SumLeft {n₁}{k}) (N.≤SumRight {n₁ N+ k}{n})
              [1] : f k ≤ g m
              [1] = ≤-trans p (increasing-monotone g↑ (N.≤SumLeft {n}))
              [2] : f' k ≤ g' m
              [2] = ≤-trans p₁ (increasing-monotone g'↑ [0])
 limMax[,]~-mono u v (lim-lim r rspec) (trunc q q₁ i) =
  isProp→PathP (λ i → ≤-trunc) (limMax[,]~-mono u v (lim-lim r rspec) q)
                               (limMax[,]~-mono u v (lim-lim r rspec) q₁) i
 limMax[,]~-mono u v (trunc p q i) r =
  isProp→PathP (λ i → ≤-trunc) (limMax[,]~-mono u v p r)
                               (limMax[,]~-mono u v q r) i

 max-zero-unique : {x y z  : Brw} → y ≤ zero → limMax[ x , y ]~ z → z ≡ ⇓ x
 max-zero-unique p zero-zero = refl
 max-zero-unique p (zero-succ r) = ⊥.rec (succ≰zero p)
 max-zero-unique p (zero-lim t tspec) = ⊥.rec (lim≰zero p)
 max-zero-unique p (succ-zero r) = max-zero-unique p r
 max-zero-unique p (succ-succ r) = ⊥.rec (succ≰zero p)
 max-zero-unique p (succ-lim r) = max-zero-unique p r
 max-zero-unique p (lim-zero l lspec) = refl
 max-zero-unique p (lim-succ r) = ⊥.rec (succ≰zero p)
 max-zero-unique p (lim-lim r rspec) = ⊥.rec (lim≰zero p)
 max-zero-unique p (trunc u v i) =
  isProp→PathP (λ i → trunc _ _) (max-zero-unique p u) (max-zero-unique p v) i

 zero-max-unique : {x y z  : Brw} → y ≤ zero → limMax[ y , x ]~ z → z ≡ ⇓ x
 zero-max-unique p zero-zero = refl
 zero-max-unique p (zero-succ r) = zero-max-unique p r
 zero-max-unique p (zero-lim t tspec) = refl
 zero-max-unique p (succ-zero r) = ⊥.rec (succ≰zero p)
 zero-max-unique p (succ-succ r) = ⊥.rec (succ≰zero p)
 zero-max-unique p (succ-lim r) = ⊥.rec (succ≰zero p)
 zero-max-unique p (lim-zero l lspec) = ⊥.rec (lim≰zero p)
 zero-max-unique p (lim-succ r) = zero-max-unique p r
 zero-max-unique p (lim-lim r rspec) = ⊥.rec (lim≰zero p)
 zero-max-unique p (trunc u v i) =
  isProp→PathP (λ i → trunc _ _) (zero-max-unique p u) (zero-max-unique p v) i


-- limMax[,] is a total relation

max-zero-defined : (x : Brw) → limMax[ zero , x ]~ (⇓ x)
max-zero-defined = Brw-ind (λ x → limMax[ zero , x ]~ (⇓ x))
                           (λ _ → trunc)
                           zero-zero
                           zero-succ
                           (λ {f} → zero-lim (λ z → ⇓ (f z)))

zero-max-defined : (x  : Brw) → limMax[ x , zero ]~ (⇓ x)
zero-max-defined  = Brw-ind (λ x → limMax[ x , zero ]~ (⇓ x))
                            (λ x → trunc)
                            zero-zero
                            succ-zero
                            (λ {f} → lim-zero (λ z → ⇓ (f z)))

limMax[]~-single-valued : {x y z z' : Brw}
                        → limMax[ x , y ]~ z → limMax[ x , y ]~ z' → z ≡ z'
limMax[]~-single-valued ρ σ =
 ≤-antisym (limMax[,]~-mono ≤-refl ≤-refl ρ σ) (limMax[,]~-mono ≤-refl ≤-refl σ ρ)

limMax[]~-outputs-unique : {x y : Brw} → isProp (Σ[ z ∈ Brw ] limMax[ x , y ]~ z)
limMax[]~-outputs-unique (z , r) (z' , r') =
 Σ≡Prop (λ x' → trunc) (limMax[]~-single-valued r r')

limMax[]~-total : (x y : Brw) → Σ[ z ∈ Brw ] limMax[ x , y ]~ z
limMax[]~-total =
 Brw-ind P (λ x → isPropΠ (λ x → limMax[]~-outputs-unique)) P₀ Pₛ Pₗ
  where
   P : Brw → Type
   P x = (y : Brw) →  Σ[ z ∈ Brw ] limMax[ x , y ]~ z

   P₀ : P zero
   P₀ y = ⇓ y , max-zero-defined y

   Pₛ : {x : Brw} → P x → P (succ x)
   Pₛ {x} ih = Brw-ind Q (λ y → limMax[]~-outputs-unique) Q₀ Qₛ Qₗ
    where
     Q : Brw → Type
     Q y = Σ[ z ∈ Brw ] limMax[ succ x , y ]~ z
     Q₀ : Q zero
     Q₀ = fst (ih zero) , succ-zero (snd (ih zero))
     Qₛ : {y : Brw} → Q y → Q (succ y)
     Qₛ {y} ih' = fst (ih y) , succ-succ (snd (ih y))
     Qₗ : {g : ℕ → Brw} {g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
     Qₗ {g} {g↑} ih' = fst (ih (limit g)) , succ-lim (ih (limit g) .snd)

   Pₗ : {f : ℕ → Brw} {f↑ : increasing f} → ((k : ℕ) → P (f k)) → P (limit f {f↑})
   Pₗ {f} {f↑} ih = Brw-ind Q (λ y → limMax[]~-outputs-unique) Q₀ Qₛ Qₗ
    where
     Q : Brw → Type
     Q y = Σ[ z ∈ Brw ] limMax[ limit f , y ]~ z
     Q₀ : Q zero
     Q₀ = limit f , lim-zero (λ z → fst (ih z zero)) (λ n → snd (ih n zero))
     Qₛ : {y : Brw} → Q y → Q (succ y)
     Qₛ {y} ih' = fst ih' , lim-succ (snd ih')
     Qₗ : {g : ℕ → Brw} {g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
     Qₗ {g} {g↑} ih' = limit (λ n → r n + ι n) , lim-lim r rspec
      where
       r : ℕ → Brw
       r n = fst (ih n (g n))
       rspec : (n : ℕ) → limMax[ f n , g n ]~ r n
       rspec n = snd (ih n (g n))

-- Definition of limMax as a function

limMax : Brw → Brw → Brw
limMax x y = fst (limMax[]~-total x y)

limMax-spec : (x y : Brw) → limMax[ x , y ]~ limMax x y
limMax-spec x y = snd (limMax[]~-total x y)

limMax-mono : {x x' y y' : Brw} → x ≤ x' → y ≤ y' → limMax x y ≤ limMax x' y'
limMax-mono {x} {x'} {y} {y'} u v =
 limMax[,]~-mono u v (limMax-spec x y) (limMax-spec x' y')


-- Properties of limMax

limMax-lim-succ : (x : Brw)(f : ℕ → Brw){f↑ : increasing f}
                → limMax (limit f {f↑}) x ≡ limMax (limit f {f↑}) (succ x)
limMax-lim-succ x f = refl

limMax-⇓-left : (x y : Brw) → ⇓ x ≤ limMax x y
limMax-⇓-left  = Brw-ind P ( λ _ → isPropΠ λ _ → ≤-trunc) P₀ Pₛ Pₗ
 where
  P : Brw → Type
  P x = (y : Brw) → ⇓ x ≤ limMax x y

  P₀ : P zero
  P₀ y = ≤-zero

  Pₛ : {x : Brw} → P x → P (succ x)
  Pₛ {x} ih = Brw-ind Q (λ _ → ≤-trunc) Q₀ Qₛ Qₗ
   where
    Q : Brw → Type
    Q y = ⇓ x ≤ limMax (succ x) y
    Q₀ : Q zero
    Q₀ = ih zero
    Qₛ : {y : Brw} → Q y → Q (succ y)
    Qₛ {y} ih' = ih y
    Qₗ : {g : ℕ → Brw} {g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
    Qₗ {g} ih' = ih (limit g)

  Pₗ : {g : ℕ → Brw} {g↑ : increasing g} → ((k : ℕ) → P (g k)) → P (limit g {g↑})
  Pₗ {g} {g↑} ih = Brw-ind Q (λ _ → ≤-trunc) Q₀ (λ {x} → Qₛ {x}) Qₗ
   where
    Q : Brw → Type
    Q y = (limit g {g↑}) ≤ limMax (limit g {g↑}) y
    Q₀ : Q zero
    Q₀ = ≤-refl
    Qₛ : {y : Brw} → Q y → Q (succ y)
    Qₛ {y} ih' = ih'
    Qₗ : {h : ℕ → Brw} {h↑ : increasing h} → ((k : ℕ) → Q (h k)) → Q (limit h {h↑})
    Qₗ {h} {h↑} ih' = limMax[,]~-mono ≤-refl
                                      ≤-zero
                                      (zero-max-defined (limit g))
                                      (limMax-spec (limit g) (limit h))

limMax-left : (x : Brw){y : Brw}(α : ℕ → Brw){ α↑ : increasing α }
            → limit α {α↑} ≤ x → limit α {α↑} ≤ limMax x y
limMax-left x {y} f p = ≤-trans (lim≤x→lim≤⇓x x f p) (limMax-⇓-left x y)

limMax-⇓-right : (x y : Brw) → ⇓ y ≤ limMax x y
limMax-⇓-right = Brw-ind P (λ x → isPropΠ (λ y → ≤-trunc)) P₀ Pₛ Pₗ
 where
  P : Brw → Type
  P x = (y : Brw) → ⇓ y ≤ limMax x y

  P₀ : P zero
  P₀ y = ≤-refl
  Pₛ : {x : Brw} → P x → P (succ x)
  Pₛ {x} ih = Brw-ind Q (λ y → ≤-trunc) ≤-zero Qₛ Qₗ
   where
    Q : Brw → Type
    Q y = ⇓ y ≤ limMax (succ x) y
    Qₛ : {y : Brw} → Q y → Q (succ y)
    Qₛ {y} ih' = ih y
    Qₗ : {f : ℕ → Brw} {f↑ : increasing f}
       → ((k : ℕ) → ⇓ (f k) ≤ limMax (succ x) (f k))
       → ⇓ (limit f {f↑}) ≤ limMax (succ x) (limit f {f↑})
    Qₗ {f} {f↑} _ = ih (limit f {f↑})
  Pₗ : {f : ℕ → Brw} {f↑ : increasing f} → ((k : ℕ) → P (f k)) → P (limit f {f↑})
  Pₗ {f} {f↑} ih = Brw-ind Q (λ y → ≤-trunc) Q₀ (λ {y} → Qₛ {y}) Qₗ
   where
    Q : Brw → Type
    Q y = ⇓ y ≤ limMax (limit f) y
    Q₀ : Q zero
    Q₀ = ≤-zero
    Qₛ : {y : Brw} → Q y → Q (succ y)
    Qₛ {y} ih' = ih'
    Qₗ : {g : ℕ → Brw} {g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
    Qₗ {g} {g↑} ih' = ≤-trans (ih 0 (limit g))
                              (limMax-mono (≤-cocone-simple f) ≤-refl)


limMax-right : (y : Brw){x : Brw}(f : ℕ → Brw){f↑ : increasing f}
             → limit f {f↑} ≤ y → limit f {f↑} ≤ limMax x y
limMax-right x {y} f p = ≤-trans (lim≤x→lim≤⇓x x f p) (limMax-⇓-right y x)

limMax-zero-left : (x : Brw) → limMax zero x ≤ x
limMax-zero-left x = limMax zero x ≤⟨ ≤-refl-≡ [1] ⟩
                     ⇓ x           ≤⟨ ⇓x≤x x ⟩
                     x             ≤∎
 where
  [1] : limMax zero x ≡ ⇓ x
  [1] = zero-max-unique ≤-zero (limMax-spec zero x)

limMax-zero-right : (x : Brw) → limMax x zero ≤ x
limMax-zero-right x = limMax x zero ≤⟨ ≤-refl-≡ [1] ⟩
                      ⇓ x           ≤⟨ ⇓x≤x x ⟩
                      x             ≤∎
 where
  [1] : limMax x zero ≡ ⇓ x
  [1] = max-zero-unique ≤-zero (limMax-spec x zero)

limMax-succ-right : (x y : Brw) → limMax x (succ y) ≡ limMax x y
limMax-succ-right = Brw-ind P (λ x → isPropΠ (λ y → trunc _ _)) P₀ Pₛ Pₗ
 where
  P : Brw → Type
  P x = (y : Brw) → limMax x (succ y) ≡ limMax x y
  P₀ : P zero
  P₀ y = refl
  Pₛ : {x : Brw} → P x → P (succ x)
  Pₛ {x} ih = Brw-ind Q (λ y → Brw-is-set _ _) Q₀ Qₛ Qₗ
   where
    Q : Brw → Type
    Q y =  limMax x y ≡ limMax (succ x) y
    Q₀ : Q zero
    Q₀ = refl
    Qₛ : {y : Brw} → Q y → Q (succ y)
    Qₛ {y} ih' = ih y
    Qₗ : {h : ℕ → Brw}{h↑ : increasing h} → ((k : ℕ) → Q (h k)) → Q (limit h {h↑})
    Qₗ {h} {h↑} ih' = refl
  Pₗ : {h : ℕ → Brw} {h↑ : increasing h} → ((k : ℕ) → P (h k)) → P (limit h {h↑})
  Pₗ {h} {h↑} ih y = refl

limMax-succ-left : (x y : Brw) → limMax (succ x) y ≡ limMax x y
limMax-succ-left x = Brw-ind (λ y → limMax (succ x) y ≡ limMax x y)
                             (λ _ → Brw-is-set _ _)
                             refl
                             (λ {y} ih → sym (limMax-succ-right x y))
                             (λ ih → refl)


limMax-lim-above-ω·k+1 : (k : ℕ)
                       → (f g : ℕ → Brw){f↑ : increasing f}{g↑ : increasing g}
                       → ω · ι (suc k) ≤ limMax (limit f {f↑}) (limit g {g↑})
                       → ∃[ n ∈ ℕ ] ω · ι k ≤ limMax (f n) (g n)
limMax-lim-above-ω·k+1 zero f g _ = ∣ zero , ≤-zero ∣
limMax-lim-above-ω·k+1 (suc k) f g q =
 ∥-∥map α (lim≤lim→weakly-bisimilar _ _ q zero)
  where
   α : Σ[ n ∈ ℕ ] ω · ι (suc k) ≤ limMax (f n) (g n) + ι n
     → Σ[ n ∈ ℕ ] ω · ι (suc k) ≤ limMax (f n) (g n)
   α (n , p) = n , cancel-finite-lim-≤ (ω · ι (suc k))
                                       (limMax (f n) (g n))
                                       (ω·k-islim' (suc k) (≤-succ-mono ≤-zero)) n p

ω·k-≤-⊎-closure : (k : ℕ) → (x y : Brw)
                 → ω · ι k ≤ limMax x y
                 → ∥ (ω · ι k ≤ x) ⊎ (ω · ι k ≤ y) ∥
ω·k-≤-⊎-closure zero x y p = ∣ inl ≤-zero ∣
ω·k-≤-⊎-closure (suc k) =
 Brw-ind P (λ x → isPropΠ (λ y → isProp→ isPropPropTrunc)) P₀ Pₛ Pₗ
  where
   Q : Brw → Brw → Type
   Q x y = ω · ι (suc k) ≤ limMax x y → ∥ (ω · ι (suc k) ≤ x) ⊎ (ω · ι (suc k) ≤ y) ∥

   P : Brw → Type
   P x = (y : Brw) → Q x y

   P₀ : P zero
   P₀ y p = ∣ inr (≤-trans p (limMax-zero-left y)) ∣

   Pₛ : {x : Brw} → P x → P (succ x)
   Pₛ {x} ih y p = ∥-∥map (⊎.map (λ a → ≤-trans a ≤-succ-incr-simple) (λ a → a))
                          (ih y (≤-trans p (≤-refl-≡ (limMax-succ-left x y))))

   Pₗ : {h : ℕ → Brw}{h↑ : increasing h} → ((k : ℕ) → P (h k)) → P (limit h {h↑})
   Pₗ {h} {h↑} ih =
    Brw-ind (Q (limit h {h↑})) (λ x → isProp→ isPropPropTrunc) Q₀ Qₛ Qₗ
     where
      Q₀ : Q (limit h {h↑}) zero
      Q₀ p = ∣ inl (≤-trans p ≤-refl) ∣

      Qₛ : {y : Brw} → Q (limit h {h↑}) y → Q (limit h {h↑}) (succ y)
      Qₛ {y} ih' p =
       ∥-∥map (⊎.map (λ a → a) (λ a → ≤-trans a ≤-succ-incr-simple)) (ih' p)

      -- the interesting case, where both x and y are limits:
      Qₗ : {s : ℕ → Brw} {s↑ : increasing s}
         → ((k : ℕ) → Q (limit h {h↑}) (s k)) → Q (limit h {h↑}) (limit s {s↑})
      Qₗ {s} {s↑} ih' p =
       ∥-∥rec isPropPropTrunc τ (∥-∥map γ (limMax-lim-above-ω·k+1 k h s p))
        where
         τ : Σ[ n ∈ ℕ ] ∥ (ω · ι k ≤ (h n)) ⊎ (ω · ι k ≤ (s n)) ∥
           → ∥ (ω · ι (suc k) ≤ (limit h {h↑})) ⊎ (ω · ι (suc k) ≤ (limit s {s↑})) ∥
         τ (n , p) =
          ∥-∥map (⊎.map (limit-reach-next-ω h k n) (limit-reach-next-ω s k n)) p
         γ : Σ[ n ∈ ℕ ] ω · ι k ≤ (limMax (h n) (s n))
           → Σ[ n ∈ ℕ ] ∥ (ω · ι k ≤ (h n)) ⊎ (ω · ι k ≤ (s n)) ∥
         γ (n₀ , z) = n₀ , ω·k-≤-⊎-closure k (h n₀) (s n₀) z


-- Definition of limMax over Brwᶻˡ

limMax-is-zl : (x y : Brw) → Brw-zero-or-limit (limMax x y)
limMax-is-zl =
 Brw-ind P (λ z → isPropΠ (λ b → isPropBrw-zero-or-limit _)) P₀ (λ {s} → Pₛ {s}) Pₗ
  where
   P : Brw → Type
   P x = (y : Brw) → Brw-zero-or-limit (limMax x y)

   P₀ : P zero
   P₀ y = ⇓-Islim⊎zero y

   Pₛ : {x : Brw} → P x → P (succ x)
   Pₛ {x} ih = Brw-ind Q (λ z → isPropBrw-zero-or-limit _) Q₀ Qₛ Qₗ
    where
     Q : Brw → Type
     Q y = Brw-zero-or-limit (limMax (succ x) y)
     Q₀ : Q zero
     Q₀ = ih zero
     Qₛ : {y : Brw} → Q y → Q (succ y)
     Qₛ {y} ih' = ih y
     Qₗ : {g : ℕ → Brw}{g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
     Qₗ {g} {g↑} ih' = ih (limit g)

   Pₗ : {f : ℕ → Brw} {f↑ : increasing f} → ((k : ℕ) → P (f k)) → P (limit f {f↑})
   Pₗ {f} {f↑} ih = Brw-ind Q (λ b → isPropBrw-zero-or-limit _) Q₀ (λ {s} → Qₛ {s}) Qₗ
    where
     Q : Brw → Type
     Q y = Brw-zero-or-limit (limMax (limit f) y)
     Q₀ : Q zero
     Q₀ = inl ∣ (f , f↑) , (limit-is-sup f f↑) ∣
     Qₛ : {y : Brw} → Q y → Q (succ y)
     Qₛ {y} ih' = ih'
     Qₗ : {g : ℕ → Brw}{g↑ : increasing g} → ((k : ℕ) → Q (g k)) → Q (limit g {g↑})
     Qₗ {g} {g↑} ih' =
      inl ∣ ((λ n → r n + ι n) , r↑) , limit-is-sup (λ z → r z + ι z) r↑ ∣
       where
        r : ℕ → Brw
        r n = limMax (f n) (g n)
        rspec : (n : ℕ) → limMax[ f n , g n ]~ r n
        rspec n = limMax-spec (f n) (g n)
        r↑ : increasing (λ n → r n + ι n)
        r↑ n = ≤-succ-mono (+x-mono (ι n)
                                    (limMax[,]~-mono (<-in-≤ (f↑ n))
                                                     (<-in-≤ (g↑ n))
                                                     (rspec n)
                                                     (rspec (suc n))))

limMaxᶻˡ : Brwᶻˡ →  Brwᶻˡ →  Brwᶻˡ
limMaxᶻˡ (x , hx) (y , hy) = limMax x y , limMax-is-zl x y

ordinal-dec-∨-aux₁ : {ℓ : Level} (k : ℕ) (P Q : Type ℓ)
                   → ordinal-dec (ω · ι (suc k)) P
                   → ordinal-dec (ω · ι (suc k)) Q
                   → ordinal-dec (ω · ι (suc k)) ∥ P ⊎ Q ∥
ordinal-dec-∨-aux₁ k P Q = ∥-∥map2 [1]
 where
  k' = suc k
  [1] : ordinal-dec-str (ω · ι k') P
      → ordinal-dec-str (ω · ι k') Q
      → ordinal-dec-str (ω · ι k') ∥ P ⊎ Q ∥
  [1] (x , e₁) (y , e₂) = (limMax x y , [2] , [3])
   where
    [2] : ∥ P ⊎ Q ∥ → ω · ι k' ≤ limMax x y
    [2] = ∥-∥rec ≤-trunc [2]'
     where
      [2]' : P ⊎ Q → ω · ι k' ≤ limMax x y
      [2]' (inl p) = limMax-left  x {y} (λ n → ω · ι k + ι n) (lr e₁ p)
      [2]' (inr q) = limMax-right y {x} (λ n → ω · ι k + ι n) (lr e₂ q)
    [3] : ω · ι k' ≤ limMax x y → ∥ P ⊎ Q ∥
    [3] l = ∥-∥map [4] (ω·k-≤-⊎-closure k' x y l)
     where
      [4] : (ω · ι k' ≤ x) ⊎ (ω · ι k' ≤ y) → P ⊎ Q
      [4] = map (rl e₁) (rl e₂)

ordinal-dec-∨-aux₂ : {ℓ : Level} (k : ℕ) (P Q : Type ℓ) → isProp P → isProp Q
                   → ordinal-dec (ω · ι k) P
                   → ordinal-dec (ω · ι k) Q
                   → ordinal-dec (ω · ι k) ∥ P ⊎ Q ∥
ordinal-dec-∨-aux₂ zero P Q PProp QProp hP hQ =
 rl (zero-decidable-iff-true ∥ P ⊎ Q ∥ squash)
    ∣ (inl (lr (zero-decidable-iff-true P PProp) hP)) ∣
ordinal-dec-∨-aux₂ (suc k) P Q _ _ = ordinal-dec-∨-aux₁ k P Q

ordinal-dec-∨ : {ℓ : Level} (k n : ℕ) (P Q : Type ℓ) → isProp P → isProp Q
              → ordinal-dec (ω · ι k + ι n) P
              → ordinal-dec (ω · ι k + ι n) Q
              → ordinal-dec (ω · ι k + ι n) ∥ P ⊎ Q ∥
ordinal-dec-∨ k zero = ordinal-dec-∨-aux₂ k
ordinal-dec-∨ k (suc n) P Q PProp QProp hP hQ =
 rl (ordinal-dec-equivalent-lim-benchmark ∥ P ⊎ Q ∥ squash (ω · ι k + ι n'))
    [6]
  where
   n' = suc n
   k' = suc k

   eq = (ω · ι k + ι n) + ω  ≡⟨ sym (+-assoc ω) ⟩
         ω · ι k + (ι n + ω) ≡⟨ cong (ω · ι k +_) (+ω-absorbs-finite n) ⟩
         ω · ι k + ω         ∎

   [1] : ordinal-dec ((ω · ι k + ι n) + ω) P
   [1] = lr (ordinal-dec-equivalent-lim-benchmark P PProp (ω · ι k + ι n')) hP

   [2] : ordinal-dec ((ω · ι k + ι n) + ω) Q
   [2] = lr (ordinal-dec-equivalent-lim-benchmark Q QProp (ω · ι k + ι n')) hQ

   [3] : ordinal-dec (ω · ι k') P
   [3] = subst (λ - → ordinal-dec - P) eq [1]

   [4] : ordinal-dec (ω · ι k') Q
   [4] = subst (λ - → ordinal-dec - Q) eq [2]

   [5] : ordinal-dec (ω · ι k') ∥ P ⊎ Q ∥
   [5] = ordinal-dec-∨-aux₂ k' P Q PProp QProp [3] [4]

   [6] : ordinal-dec ((ω · ι k + ι n) + ω) ∥ P ⊎ Q ∥
   [6] = subst (λ - → ordinal-dec - ∥ P ⊎ Q ∥) (sym eq) [5]
