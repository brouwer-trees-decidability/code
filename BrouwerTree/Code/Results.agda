----------------------------------------------------------------------------------------------------
-- Some results of using the Code family of ≤ on Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Code.Results where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum

-- open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)

open import PropTrunc

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Code

open import Iff
open import General-Properties


{- Inequality between limits is equivalent to weak simulation -}

lim≤lim→weakly-bisimilar : ∀ f {f↑} g {g↑} → (limit f {f↑} ≤ limit g {g↑}) → f ≲ g
lim≤lim→weakly-bisimilar f {f↑} g {g↑} ⊔f≤⊔g = λ k →
  ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (f k) (g n)}
         {P = ∥ Σ ℕ (λ n → f k ≤ g n) ∥}
         isPropPropTrunc
         (λ {(n , c-fk≤gn) → ∣ (n , Code→≤ c-fk≤gn) ∣})
         (≤→Code ⊔f≤⊔g k)

weakly-bisimilar→lim≤lim : ∀ f {f↑} g {g↑} → f ≲ g → (limit f {f↑} ≤ limit g {g↑})
weakly-bisimilar→lim≤lim f {f↑} g {g↑} f≤g =
    ≤-limiting f (λ k → ∥-∥rec ≤-trunc (λ (n , fk≤gn) → ≤-cocone g fk≤gn) (f≤g k))

lim≤lim↔weakly-bisimilar : ∀ f {f↑} g {g↑} → (limit f {f↑} ≤ limit g {g↑}) ↔ f ≲ g
lim≤lim↔weakly-bisimilar f g = lim≤lim→weakly-bisimilar f g , weakly-bisimilar→lim≤lim f g

≤-succ-mono⁻¹ : ∀ {x y} → succ y ≤ succ x → y ≤ x
≤-succ-mono⁻¹ {x} {y} sy≤sx = Code→≤ (≤→Code sy≤sx)

≤-succ-mono-↔ : ∀ {x y} → succ y ≤ succ x ↔ y ≤ x
≤-succ-mono-↔ = (≤-succ-mono⁻¹ , ≤-succ-mono)

<-succ-mono : ∀ {x y} → y < x → succ y < succ x
<-succ-mono = ≤-succ-mono

<-succ-mono⁻¹ : ∀ {x y} → succ y < succ x → y < x
<-succ-mono⁻¹ = ≤-succ-mono⁻¹

<-cocone-simple : ∀ f {f↑} {k} → f k < limit f {f↑}
<-cocone-simple f {f↑} {k} = <∘≤-in-< (f↑ k) (≤-cocone-simple f {f↑} {suc k})

-- If a limit is below `succ x`, then it is already below `x`
lim≤sx→lim≤x : ∀ f x {f↑} → limit f {f↑} ≤ succ x → limit f {f↑} ≤ x
lim≤sx→lim≤x f x {f↑} ⊔f≤sx =
    ≤-limiting f {f↑} (λ k → ≤-succ-mono⁻¹ {x} {f k}
                                           (succ (f k) ≤⟨ f↑ k ⟩
                                            f (suc k)  ≤⟨ ≤-cocone-simple f ⟩
                                            limit f    ≤⟨ ⊔f≤sx ⟩
                                            succ x     ≤∎))

-- similarly for being strictly below
lim<sx→lim≤x : ∀ f x {f↑} → limit f {f↑} < succ x → limit f {f↑} ≤ x
lim<sx→lim≤x f x {f↑} ⊔f<sx = ≤-succ-mono⁻¹ (⊔f<sx)


lim≤sx↔lim≤x : ∀ f x {f↑} → limit f {f↑} ≤ succ x ↔ limit f {f↑} ≤ x
lim≤sx↔lim≤x f x = lim≤sx→lim≤x f x , ≤-succ-incr

-- If something is strictly below the limit of f, then it is strictly
-- below some f n. This corresponds to the succ-limit case.
below-limit-lemma : ∀ x f {f↑} → x < limit f {f↑} → ∥ Σ ℕ (λ n → x < f n) ∥
below-limit-lemma x f {f↑} x<⊔f =
  ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (succ x) (f n)}
         {P = ∥ Σ ℕ (λ n → x < f n) ∥}
         isPropPropTrunc
         (λ {(n , c-sx≤fn) → ∣ n , Code→≤ c-sx≤fn ∣})
         (≤→Code {succ x} {limit f} x<⊔f )

below-limit-↔ : ∀ x f {f↑} → x < limit f {f↑} ↔ ∥ Σ ℕ (λ n → x < f n) ∥
below-limit-↔ x f =
 below-limit-lemma x f , ∥-∥rec isProp⟨<⟩ λ (n , l) → <-trans _ _ _ l (<-cocone-simple f)

-- limits are closed under successors
x<lim→sx<lim : ∀ f x {f↑} → x < limit f {f↑} → succ x < limit f {f↑}
x<lim→sx<lim f x {f↑} p = ∥-∥rec isProp⟨<⟩ (λ { (n , x<fn) → ≤-cocone f {k = suc n} (≤∘<-in-< x<fn (f↑ n)) }) (below-limit-lemma x f p)

x<lim↔sx<lim : ∀ f x {f↑} → x < limit f {f↑} ↔ succ x < limit f {f↑}
x<lim↔sx<lim f x = (x<lim→sx<lim f x , λ p → ≤-trans ≤-succ-incr-simple p)

{- Wellfoundedness -}

smaller-accessible : (x : Brw) → Acc _<_ x → ∀ y → y ≤ x → Acc _<_ y
smaller-accessible x is-acc⟨x⟩ y y≤x = acc (λ y' y'<y → access is-acc⟨x⟩ y' (<∘≤-in-< y'<y y≤x))

<-is-wellfounded : isWellFounded _<_
<-is-wellfounded =
  Brw-ind (λ x → Acc _<_ x)
          (λ x → isPropAcc x)
          (acc (λ y y<zero → ⊥.rec (succ≰zero y<zero)))
          (λ {x} x-acc → acc (λ y y<sx → smaller-accessible x x-acc y (≤-succ-mono⁻¹ y<sx)))
          (λ {f} {f↑} f-acc → acc (λ y y<⊔f →
             ∥-∥rec {A = Σ[ n ∈ ℕ ] y < f n}
                    {P = Acc _<_ y}
                    (isPropAcc y)
                    (λ {(n , y<fn) → smaller-accessible (f n) (f-acc n) y (<-in-≤ y<fn)})
                    (below-limit-lemma y f {f↑} y<⊔f)))

<-irreflexive : ∀ x → (x < x) → ⊥
<-irreflexive = wellfounded→irreflexive <-is-wellfounded

<-irreflexive-≡ : ∀ {x y} → x ≡ y → (x < y) → ⊥
<-irreflexive-≡ {x} p = subst (λ z → x < z → ⊥) p (<-irreflexive x)

isProp⟨<⊎≡⟩ : ∀ {x y} → (p q : (x < y) ⊎ (x ≡ y)) → p ≡ q
isProp⟨<⊎≡⟩ (inl p) (inl q) = cong inl (isProp⟨<⟩ p q)
isProp⟨<⊎≡⟩ (inl p) (inr q) = ⊥.rec (<-irreflexive-≡ q p)
isProp⟨<⊎≡⟩ (inr p) (inl q) = ⊥.rec (<-irreflexive-≡ p q)
isProp⟨<⊎≡⟩ (inr p) (inr q) = cong inr (Brw-is-set _ _ p q)


{- Antisymmetry -}

≤-antisym : ∀ {x y} -> x ≤ y -> y ≤ x -> x ≡ y
≤-antisym {x} {y} =
  Brw-ind (λ x → ∀ y → x ≤ y -> y ≤ x -> x ≡ y)
          (λ x → isPropΠ (λ y → isProp→ (isProp→ (Brw-is-set _ _))))
          (Brw-ind (λ y → zero ≤ y -> y ≤ zero -> zero ≡ y)
                   (λ y → isProp→ (isProp→ (Brw-is-set _ _)))
          (λ _ _ → refl)
          (λ _ x≤y y≤x → ⊥.rec (succ≰zero y≤x))
          (λ _ x≤y y≤x → ⊥.rec (lim≰zero y≤x)))
          (λ {x} ih →
             Brw-ind (λ y → succ x ≤ y -> y ≤ succ x -> succ x ≡ y)
                     (λ y → isProp→ (isProp→ (Brw-is-set _ _)))
                     (λ x≤y y≤x → ⊥.rec (succ≰zero x≤y))
                     (λ {y} _ sx≤sy sy≤sx →
                        cong succ (ih y (≤-succ-mono⁻¹ sx≤sy) (≤-succ-mono⁻¹ sy≤sx)))
                     (λ {g} {g↑} _ x≤y y≤x →
                        ⊥.rec (<-irreflexive _ (≤-trans x≤y (lim≤sx→lim≤x g x {g↑} y≤x)))))
          (λ {f} {f↑} _ →
             Brw-ind (λ y → limit f {f↑} ≤ y -> y ≤ limit f {f↑} -> limit f {f↑} ≡ y)
                     (λ y → isProp→ (isProp→ (Brw-is-set _ _)))
                     (λ x≤y y≤x → ⊥.rec (lim≰zero x≤y))
                     (λ {y} _ x≤y y≤x →
                        ⊥.rec (<-irreflexive _ (≤-trans y≤x (lim≤sx→lim≤x f y {f↑} x≤y))))
                     (λ {g} {g↑} _ lf≤lg lg≤lf →
                        bisim f {f↑} g {g↑} (lim≤lim→weakly-bisimilar f g lf≤lg ,
                                             lim≤lim→weakly-bisimilar g f lg≤lf)))
          x y

{- Extensionality -}

<-semi-extensional : (a b : Brw) → (∀ c → (c < a) → (c < b)) → a ≤ b
<-semi-extensional =
 Brw-ind (λ a → (b : Brw) → (∀ c → (c < a) → (c < b)) → a ≤ b)
         (λ a → isPropΠ2 (λ b _ → ≤-trunc))
         (λ b _ → ≤-zero)
         (λ {x} _ b h → h x ≤-refl)
         (λ {f} {f↑} IH b h → ≤-limiting f
                               (λ k → IH k b
                                    (λ c l → h c
                                               (<-trans _ _ _
                                                        l (<-cocone-simple f)))))

<-extensional : (a b : Brw) → (∀ c → (c < a) ↔ (c < b)) → a ≡ b
<-extensional a b h = ≤-antisym (<-semi-extensional a b (fst ∘ h))
                                (<-semi-extensional b a (snd ∘ h))


≤-extensional : (a b : Brw) → (∀ c → (c ≤ a) ↔ (c ≤ b)) → a ≡ b
≤-extensional a b h = ≤-antisym (fst (h a) ≤-refl) (snd (h b) ≤-refl)

succ-injective : ∀ {x y} → succ y ≡ succ x → y ≡ x
succ-injective p = ≤-antisym (≤-succ-mono⁻¹ (≤-refl-≡ p)) (≤-succ-mono⁻¹ (≤-refl-≡ (sym p)))

ι-reflecting : {n m : ℕ} → ι n ≤ ι m → n N.≤ m
ι-reflecting {zero} {zero} p = N.≤-refl
ι-reflecting {zero} {suc m} p = N.zero-≤
ι-reflecting {suc n} {zero} p = subst (λ z → z N.≤ zero) (sym (ι-injective (x≤zero→x≡zero p))) N.≤-refl
ι-reflecting {suc n} {suc m} p = N.suc-≤-suc (ι-reflecting {n} {m} (≤-succ-mono⁻¹ p))

lim≰ι : ∀ {f f↑} {k} → limit f {f↑} ≤ ι k → ⊥
lim≰ι p = <-irreflexive _ (≤∘<-in-< p ι _ <lim)

-- ω is the smallest limit

ω-smallest : ∀ f {f↑ : increasing f} → ω ≤ limit f {f↑}
ω-smallest f {f↑} = weakly-bisimilar→lim≤lim ι f λ k → ∣ k , ι-pointwise-smaller f f↑ k ∣
