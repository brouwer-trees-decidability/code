

{-# OPTIONS --cubical --erasure --guardedness  #-}

module BrouwerTree.OrdinalDecidability.LPOMinMax where

open import Cubical.Data.Nat
  using (ℕ; zero; suc)
  renaming (_+_ to _N+_)
import Cubical.Data.Nat.Order as N
import Cubical.Data.Nat.Properties as N
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum renaming (rec to sumrec ; map to summap)
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Relation.Nullary.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import General-Properties

open import Bool as B
open import BooleanSequence

open import PropTrunc
open import Iff

open import BrouwerTree.Everything
open import BrouwerTree.OrdinalDecidability.Basic

---------------------------LPO Results: --------------------------


-------1-LPO Result on Min Function for Brw:

BoolSeq→BrwSeq : (ℕ → Bool) → Σ[ f ∈ (ℕ → Brw) ] increasing f
BoolSeq→BrwSeq s  = f , f↑
   where
     f : ℕ → Brw
     f zero = zero
     f (suc n) with s n ≟ true
     ... | yes sn=true = f n + ω
     ... | no sn=false = f n + ι 1
     f↑ : increasing f
     f↑ k  with s k ≟ true
     ... | yes _ = ≤-cocone (λ n → f k + ι n) {_} {1} ≤-refl
     ... | no _ = ≤-refl

¬∃xPx→∀x¬Px : (s : ℕ → Bool) → ¬ (∃[ n ∈ ℕ ] s n ≡ true) → (k : ℕ) → s k ≡ false
¬∃xPx→∀x¬Px s p k with  s k ≟ true
... | yes v = ⊥.rec (p ∣ k , v ∣)
... | no u = sumrec (λ u' → ⊥.rec (u u')) (λ x → x) (dichotomyBool (s k))

Brw-Min : (x y : Brw) → Type
Brw-Min x y = Σ[ m ∈ Brw ] ((α : Brw) → ((α ≤ x) × (α ≤ y)) ↔ α ≤ m)

LPO-isProp : (s : ℕ → Bool)
           → isProp (((k : ℕ) → s k ≡ false) ⊎ (∃[ n ∈ ℕ ] s n ≡ true))
LPO-isProp s = isProp⊎ (isPropΠ (λ k → isSetBool (s k) false))
                       isPropPropTrunc
                       (λ H → ∥-∥rec (λ ()) (F H))
 where
  F : ((x : ℕ) → s x ≡ false) → ¬ (Σ[ n ∈ ℕ ] s n ≡ true)
  F h (k , hk) = true≢false (sym hk ∙ h k)

Brw-Min→LPO : (∀ (x y : Brw) → Brw-Min x y) → LPO
Brw-Min→LPO min s = fun (fst (min x y)) (snd (min x y))
  where
   y = succ ω
   f = fst (BoolSeq→BrwSeq s)
   f↑ = snd (BoolSeq→BrwSeq s)
   x = limit f {f↑}
   M : Brw
   M = fst (min x y)
   fun : (m : Brw)
         → (∀ (α : Brw) → ((α ≤ x) × (α ≤ y)) ↔ α ≤ m)
         → ((k : ℕ) → s k ≡ false) ⊎ (∃[ n ∈ ℕ ]  s n ≡ true)
   fun = Brw-ind P P-prop P₀ Pₛ Pₗ
    where
     P : Brw → Type
     P m = (∀ (α : Brw) → ((α ≤ x) × (α ≤ y)) ↔ α ≤ m)
         → ((k : ℕ) → s k ≡ false) ⊎ (∃[ n ∈ ℕ ] s n ≡ true)
     P-prop : (m : Brw) → isProp (P m)
     P-prop m = isProp→ (LPO-isProp s)
     P₀ : P zero
     P₀ hm = ⊥.rec (lim≰zero falsity)
      where
       falsity : ω ≤ zero
       falsity = fst (hm ω) ((ω-smallest f) , <-in-≤ ≤-refl)
     Pₛ : {m : Brw} → P m → P (succ m)
     Pₛ {m} e hsm = summap fun1 fun2 (<ω-or-≥ω  m)
      where
       fun2 : ω ≤ m → ∃[ n ∈ ℕ ] s n ≡ true
       fun2 ω≤m = ∥-∥rec isPropPropTrunc F2 (below-limit-lemma ω f v1)
         where
          v1 : ω < limit f {f↑}
          v1 = <∘≤-in-< (≤-succ-mono ω≤m) (fst (snd (hsm (succ m)) ≤-refl))
          F1 : Σ[ n ∈ ℕ ] ω < f n → Σ[ n ∈ ℕ ] ω ≤ f n
          F1 (n , hn) = n , <-in-≤ hn
          F : Σ[ n ∈ ℕ ] ω ≤ f n → ∃[ n ∈ ℕ ] s n ≡ true
          F2 : Σ[ n ∈ ℕ ] ω < f n → ∃[ n ∈ ℕ ] s n ≡ true
          F2 = F ∘ F1
          F (n , b) = H w
           where
            H : ∃[ k ∈ ℕ ] (k N.≤ n) × (s k ≡ true) → ∃[ n ∈ ℕ ] s n ≡ true
            H = ∥-∥map (λ (k , _ , e) → k , e)
            w : ∃[ k ∈ ℕ ] (k N.≤ n) × (s k ≡ true)
            w = lemma n b
             where
              lemma : (n : ℕ) → ω ≤ f n → ∃[ k ∈ ℕ ] (k N.≤ n) × (s k ≡ true)
              lemma zero ω≤fn = ⊥.elim (lim≰zero ω≤fn)
              lemma (suc n) ω≤fn with dec-true-below n s
              ... | yes (k , l , e) = ∣ k , N.≤-suc l , e ∣
              ... | no v' = ∥-∥map (λ (k , l , e) → k , N.≤-suc l , e)
                            (lemma n [3])
               where
                [1] : s n ≡ false
                [1] = ¬true→false (s n)(λ (e : s n ≡ true) → v'(n , N.≤-refl , e))
                [2] : ω ≤ succ (f n)
                [2] = subst (ω ≤_) (f-eq₂ n [1]) ω≤fn
                  where
                    f-eq₂ : (n : ℕ) → s n ≡ false → f (suc n) ≡ succ (f n)
                    f-eq₂ n e with s n ≟ true
                    ... | yes e' = ⊥.elim {_} {λ _ → f n + ω ≡ succ (f n)}
                                   (true≢false (sym e' ∙ e))
                    ... | no _ = refl
                [3] : ω ≤ f n
                [3] = lim≤sx→lim≤x ι (f n) [2]

       fun1 : m < ω → (k : ℕ) → s k ≡ false
       fun1 m<ω = ⊥.rec ((<-irreflexive ω) fls)
        where
         t1 : ω ≤ succ m
         t1 = fst (hsm ω) ((ω-smallest f) ,  <-in-≤ ≤-refl)
         t2 : ω ≤ m
         t2 = lim≤sx→lim≤x ι m t1
         fls : succ ω ≤ ω
         fls = ≤-trans (≤-succ-mono t2) m<ω
     Pₗ : {g : ℕ → Brw} {g↑ : increasing g}
        → ((k : ℕ) → P (g k)) → P (limit g {g↑})
     Pₗ {g} {g↑} q hg = inl (¬∃xPx→∀x¬Px s (λ H → ∥-∥rec (λ ()) fun5 H))
      where
       fun3 :  Σ[ n ∈ ℕ ] (s n ≡ true) → succ ω ≤ limit f {f↑}
       fun4 :  Σ[ n ∈ ℕ ] (s n ≡ true) → succ ω ≡  limit g {g↑}
       fun4 pn = ≤-antisym
                (fst (hg y) (fun3 pn , ≤-refl))
                (snd (snd (hg (limit g)) ≤-refl))
       fun5 :  Σ[ n ∈ ℕ ] (s n ≡ true) → ⊥
       fun5 p = succ≠lim (fun4 p)
       fun3 h = W h
        where
          W :  Σ[ n ∈ ℕ ] s n ≡ true → succ ω ≤ limit f {f↑}
          W (n₀ , sn0=t ) = ≤-cocone f {k = suc(n₀ N+ 1)}
            (≤-trans (≤-succ-mono v) (add-finite-part-lemma' f {f↑} (suc n₀) 1))
           where
             v : ω ≤ f (suc n₀)
             v with s n₀ ≟ true
             ... | yes z = ω-smallest (λ n → f (n₀) + ι n)
             ... | no  z' = ⊥.rec (z' sn0=t)
             V : Σ[ n ∈ ℕ ] ω ≤ f n
             V = (suc n₀) , v

------------------------------------------------------
----------2-LPO Result on Max function for Brwᶻˡ:

BoolSeq→BrwSeq2 : (ℕ → Bool) → Σ[ f ∈ (ℕ → Brw) ] (increasing f)
BoolSeq→BrwSeq2 s  = f , f↑
   where
     f : ℕ → Brw
     f zero = zero
     f (suc n) with s n ≟ true
     ... | yes sn=true = f n + (ω + ω)
     ... | no sn=false = f n + ι 1

     f↑ : increasing f
     f↑ k  with s k ≟ true
     ... | yes _ = ≤-cocone (λ n → f k + (ω + ι n)) {_} {1}
                  (≤-succ-mono (≤-cocone {x = f k} (λ n → f k + ι n)
                  {k = zero} (x+-increasing {x = f k} zero)))
     ... | no _ = ≤-refl

Brwᶻˡ-Max : (x y : Brwᶻˡ) → Type
Brwᶻˡ-Max x y  =  Σ[ m ∈ Brwᶻˡ ]
                  ∀ (α : Brwᶻˡ)
                  → ((fst α ≤ fst x) ⊎ (fst α ≤ fst y) ) ↔ (fst α ≤ fst m )

Brwᶻˡ-Connex : (x y : Brwᶻˡ) → Type
Brwᶻˡ-Connex x y  = (fst x ≤ fst y) ⊎ (fst y ≤ fst x)

Brwᶻˡ-Max→Brwᶻˡ-Connex : (x y : Brwᶻˡ)
                       → Brwᶻˡ-Max x y
                       → Brwᶻˡ-Connex x y
Brwᶻˡ-Max→Brwᶻˡ-Connex x y max = sumrec
                       (λ p → inr (≤-trans t2 p))
                       (λ q → inl (≤-trans t1 q))
                       t3
  where
   xx = fst x
   yy = fst y
   mxy = fst ( fst max )
   t1 : xx ≤ mxy
   t1 = fst (snd max x) (inl ≤-refl)
   t2 : yy ≤ mxy
   t2 = fst (snd max y) (inr ≤-refl)
   t3 : (mxy ≤ xx) ⊎ (mxy ≤ yy)
   t3 = snd (snd max (fst max)) ≤-refl

Brwᶻˡ-Connex→LPO : (∀ (x y : Brwᶻˡ) → Brwᶻˡ-Connex x y) → LPO
Brwᶻˡ-Connex→LPO cnvx s = sumrec (λ p → inl (Hl p))
                                 (λ q → inr (Hr q)) H
  where
   f = fst (BoolSeq→BrwSeq2 s)
   f↑ = snd (BoolSeq→BrwSeq2 s)
   ω2 : Brwᶻˡ
   ω2 = (ω + ω) , inl ω+ω-islim
   ff : Brwᶻˡ
   ff = limit f {f↑} , inl ∣  (f , f↑) , limit-is-sup f f↑  ∣
   H : (limit f {f↑} ≤ ω + ω) ⊎ (ω + ω ≤ limit f {f↑})
   H = cnvx ff ω2
   Hl : limit f {f↑} ≤ ω + ω → ∀ k → s k ≡ false
   Hl p = ¬∃xPx→∀x¬Px s (∥-∥rec (λ ()) [1])
    where
     [1] : ¬ (Σ[ n ∈ ℕ ] s n ≡ true)
     [1] (m , hm) = <-irreflexive (limit f {f↑}) (≤∘<-in-< p [3])
      where
       f-eq₁ : (n : ℕ) → s n ≡ true → f (suc n) ≡ f n + (ω + ω)
       f-eq₁ n e with s n ≟ true
       ... | yes _ = refl
       ... | no  ν = ⊥.elim {_} {λ _ → succ (f n) ≡ f n + (ω + ω)} (ν e)
       [2] : ω + ω ≤ f (suc m)
       [2] = ≤-trans (+x-increasing (ω + ω)) (≤-refl-≡ (sym (f-eq₁ m hm)))
       [3] : ω + ω < limit f {f↑}
       [3] = ≤-cocone f {k = suc (m N+ 1)} (≤-trans (≤-succ-mono [2])
            (add-finite-part-lemma' f {f↑} (suc m) 1))
   Hr : ω + ω ≤ limit f {f↑} → ∃[ n ∈ ℕ ] s n ≡ true
   Hr p = [5] [2]
    where
     [1] : (λ n → ω + ι n) ≲ f
     [1] = lim≤lim→weakly-bisimilar (λ n → ω + ι n) f p
     [2] : ∃[ n ∈ ℕ ] ω ≤ f n
     [2] = [1] zero
     [3] : (n : ℕ)  → ω ≤ f n → Σ[ m ∈ ℕ ] s m ≡ true
     [3] zero p = ⊥.rec (lim≰zero p)
     [3] (suc n) p with s n ≟ true
     ... | yes v = n , v
     ... | no u = [3] n [4]
      where
        [4] : ω ≤ f n
        [4] = lim≤sx→lim≤x ι (f n) p
     [5] : ∃[ n ∈ ℕ ] ω ≤ f n → ∃[ m ∈ ℕ ] s m ≡ true
     [5] = ∥-∥rec isPropPropTrunc (λ (m , hm) → ∣ [3] m hm ∣)

Brwᶻˡ-Max→LPO : (∀ (x y : Brwᶻˡ) → Brwᶻˡ-Max x y) → LPO
Brwᶻˡ-Max→LPO max = Brwᶻˡ-Connex→LPO (λ x y → Brwᶻˡ-Max→Brwᶻˡ-Connex x y (max x y))

------
