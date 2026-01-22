{-# OPTIONS --cubical --guardedness --erasure #-}
module BrouwerTree.OrdinalDecidability.Sierpinski where

open import Cubical.Foundations.Prelude hiding (_∨_; _∧_)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat as Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (∃; ∃-syntax; _∨_; _∧_)
open import Cubical.Data.Empty as Empty renaming (⊥ to Empty)
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function

open import Iff
open import PropTrunc

open import BrouwerTree.OrdinalDecidability.Basic

private
  variable
    ℓ ℓ' : Level

mutual

  -- The free ω-complete cpo on Unit
  data 𝕊 : Type where
    ⊤ : 𝕊
    ⊥ : 𝕊
    ⋁ : (ℕ → 𝕊) -> 𝕊
    ∨-comm : ∀ {x y} → x ∨ y ≡ y ∨ x
    ∨-assoc : ∀ {x y z} → x ∨ (y ∨ z) ≡ (x ∨ y) ∨ z
    ∨-idem : ∀ {x} → x ∨ x ≡ x
    ∨-bot : ∀ {x} → x ∨ ⊥ ≡ x
    ∨-absorb : ∀ {s : ℕ → 𝕊} n → s n ∨ (⋁ s) ≡ ⋁ s
    ∨-distr : ∀ {s : ℕ → 𝕊} {x} → x ∨ (⋁ s) ≡ ⋁ (λ n → x ∨ s n)
    isSet𝕊 : isSet 𝕊

  _∨_ : 𝕊 → 𝕊 → 𝕊
  x ∨ y = ⋁ (caseNat x y)


module _ (P : 𝕊 → Type ℓ)(isProp⟨P⟩ : (x : 𝕊) → isProp (P x))
         (p⊤ : P ⊤)(p⊥ : P ⊥)
         -- we split up the p⋁ case into head and tail to please the
         -- termination checker, due to the `caseNat`s involved
         (p⋁ : ∀ {s} → P (s 0) → ((n : ℕ) -> P (s (suc n))) → P (⋁ s))
       where

  𝕊-ind' : (x : 𝕊) -> P x
  𝕊-ind' ⊤ = p⊤
  𝕊-ind' ⊥ = p⊥
  𝕊-ind' (⋁ s) = p⋁ (𝕊-ind' (s 0)) (λ n → 𝕊-ind' (s (suc n)))
  𝕊-ind' (∨-comm {x} {y} i) =
   isProp→PathP (λ i → isProp⟨P⟩ (∨-comm i))
                (p⋁ (𝕊-ind' x) (λ n → 𝕊-ind' y))
                (p⋁ (𝕊-ind' y) (λ n → 𝕊-ind' x)) i
  𝕊-ind' (∨-assoc {x} {y} {z} i) =
   isProp→PathP (λ i → isProp⟨P⟩ (∨-assoc i))
                (p⋁ (𝕊-ind' x)
                    (λ _ → p⋁ (𝕊-ind' y) (λ _ → 𝕊-ind' z)))
                (p⋁ (p⋁ (𝕊-ind' x) (λ n → 𝕊-ind' y))
                    (λ n → 𝕊-ind' z)) i
  𝕊-ind' (∨-idem {x} i) =
   isProp→PathP (λ i → isProp⟨P⟩ (∨-idem i))
                (p⋁ (𝕊-ind' x) (λ n → 𝕊-ind' x))
                (𝕊-ind' x) i
  𝕊-ind' (∨-bot {x} i) =
   isProp→PathP (λ i → isProp⟨P⟩ (∨-bot i))
                (p⋁ (𝕊-ind' x) (λ n → p⊥))
                (𝕊-ind' x) i
  𝕊-ind' (∨-absorb {s} n i) =
   isProp→PathP (λ i → isProp⟨P⟩ (∨-absorb n i))
                (p⋁ (𝕊-ind' (s n))
                    (λ _ → p⋁ (𝕊-ind' (s 0)) (λ k → 𝕊-ind' (s (suc k)))))
                    (p⋁ (𝕊-ind' (s 0)) (λ n → 𝕊-ind' (s (suc n)))) i
  𝕊-ind' (∨-distr {s} {x} i) =
   isProp→PathP (λ i → isProp⟨P⟩ (∨-distr i))
                (p⋁ (𝕊-ind' x)
                    (λ _ → p⋁ (𝕊-ind' (s 0)) (λ n → 𝕊-ind' (s (suc n)))))
                (p⋁ (p⋁ (𝕊-ind' x)
                    (λ n → 𝕊-ind' (s 0)))
                    (λ n → p⋁ (𝕊-ind' x) (λ n₁ → 𝕊-ind' (s (suc n))))) i
  𝕊-ind' (isSet𝕊 x y p q i j) =
   isProp→SquareP (λ i j → isProp⟨P⟩ (isSet𝕊 x y p q i j))
                  (λ j → 𝕊-ind' x)
                  (λ j → 𝕊-ind' y)
                  (λ j → 𝕊-ind' (p j))
                  (λ j → 𝕊-ind' (q j)) i j

-- Of course now we can give the "proper" type for `p⋁`, post facto

𝕊-ind : (P : 𝕊 → Type ℓ)
      → ((x : 𝕊) → isProp (P x))
      → P ⊤
      → P ⊥
      → ({s : ℕ → 𝕊} → ((n : ℕ) -> P (s n)) → P (⋁ s))
      → (x : 𝕊) -> P x
𝕊-ind P isProp⟨P⟩ p⊤ p⊥ p⋁ x =
 𝕊-ind' P isProp⟨P⟩ p⊤ p⊥ (λ {s} p0 ps → p⋁ λ { zero → p0 ; (suc n) → ps n }) x

⊤-is-top : (x : 𝕊) → x ∨ ⊤ ≡ ⊤
⊤-is-top =
 𝕊-ind (λ x → x ∨ ⊤ ≡ ⊤) (λ x → isSet𝕊 (x ∨ ⊤) ⊤)
       ∨-idem
       (∨-comm ∙ ∨-bot)
       (λ {s} ih → (⋁ s ∨ ⊤)         ≡⟨ ∨-comm ⟩
                   (⊤ ∨ ⋁ s)         ≡⟨ ∨-distr ⟩
                   ⋁ (λ x → ⊤ ∨ s x) ≡⟨ cong ⋁ ([1] ih) ⟩
                   (⊤ ∨ ⊤)           ≡⟨ ∨-idem ⟩
                   ⊤                 ∎)
 where
  [1] : {s : ℕ → 𝕊} → ((n : ℕ) → (s n ∨ ⊤) ≡ ⊤)
      → (λ x → ⋁ (caseNat ⊤ (s x))) ≡ (λ v → caseNat ⊤ ⊤ v)
  [1] ih = (funExt (λ n → ∨-comm ∙ ih n)) ∙ funExt (λ { zero → refl ; (suc n) → refl })

contains-⊤-implies-is-⊤ : (s : ℕ → 𝕊)
                        → ∃[ n ∈ ℕ ] s n ≡ ⊤ → ⋁ s ≡ ⊤
contains-⊤-implies-is-⊤ s = ∥-∥rec (isSet𝕊 (⋁ s) ⊤)
                                   (λ (n , sn=⊤) → ⋁ s         ≡⟨ sym (∨-absorb n) ⟩
                                                   (s n ∨ ⋁ s) ≡⟨ ∨-comm ⟩
                                                   (⋁ s ∨ s n) ≡⟨ cong (⋁ s ∨_) sn=⊤ ⟩
                                                   (⋁ s ∨ ⊤)   ≡⟨ ⊤-is-top (⋁ s) ⟩
                                                   ⊤           ∎)

⋁-idem : {x : 𝕊} → ⋁ (λ _ → x) ≡ x
⋁-idem {x} = ⋁ (λ _ → x) ≡⟨ [1] ⟩
             (x ∨ x)     ≡⟨ ∨-idem ⟩
             x           ∎
 where
  [1] = cong ⋁ (funExt λ { zero → refl ; (suc n) → refl })

-- Same termination checker trick for `is⊥` as for `𝕊-ind`
mutual
  is⊥ : 𝕊 -> Type ℓ-zero
  is⊥ ⊤ = Empty
  is⊥ ⊥ = Unit
  is⊥ (⋁ s) = is⊥ (s 0) × (∀ n → is⊥ (s (suc n)))
  is⊥ (∨-comm {x} {y} i) =
   hPropExt (isProp× (is⊥-prop x) (isProp→ {A = ℕ} (is⊥-prop y)))
            (isProp× (is⊥-prop y) (isProp→ {A = ℕ} (is⊥-prop x)))
            (λ (p , f) → f 1 , λ _ → p)
            (λ (p , f) → f 1 , λ _ → p) i
  is⊥ (∨-assoc {x} {y} {z} i) =
   hPropExt (isProp× (is⊥-prop x)
                     (isProp→ {A = ℕ} (isProp× (is⊥-prop y)
                                      (isProp→ {A = ℕ} (is⊥-prop z)))))
            (isProp× (isProp× (is⊥-prop x)
                              (isProp→ {A = ℕ} (is⊥-prop y)))
                     (isProp→ {A = ℕ} (is⊥-prop z)))
            (λ { (a , bc) → (a , λ _ → fst (bc 1)) , λ _ → snd (bc 1) 1 })
            (λ ((a , b) , c) → a , λ _ → (b 1) , c) i
  is⊥ (∨-idem {x} i) =
   hPropExt (isProp× (is⊥-prop x) (isProp→ {A = ℕ} (is⊥-prop x)))
            (is⊥-prop x)
            fst
            (λ p → p , λ _ → p)
            i
  is⊥ (∨-bot {x} i) =
   hPropExt (isProp× (is⊥-prop x) (isProp→ {A = ℕ} isPropUnit))
            (is⊥-prop x)
            fst
            (λ p → p , λ _ → tt) i
  is⊥ (∨-absorb {s = s} n i) =
   hPropExt (isProp× (is⊥-prop (s n))
                     (isProp→ {A = ℕ}
                       (isProp× (is⊥-prop (s 0))
                                (isPropΠ {A = ℕ} (λ m → is⊥-prop (s (suc m)))))))
            (isProp× (is⊥-prop (s 0))
                     (isPropΠ {A = ℕ} (λ m → (is⊥-prop (s (suc m))))))
            (λ (sn , f) → (fst (f 1)) , (λ m → snd (f 1) m))
            (λ (sz , f) → Nat.elim {A = is⊥ ∘ s} sz (λ m _ → f m) n , λ m → sz , f) i
  is⊥ (∨-distr {s} {x} i) =
   hPropExt (isProp× (is⊥-prop x)
                     (isProp→ {A = ℕ}
                       (isProp× (is⊥-prop (s 0))
                                (isPropΠ {A = ℕ} (λ m → (is⊥-prop (s (suc m))))))))
            (isProp× (isProp× (is⊥-prop x)
                              (isProp→ {A = ℕ} (is⊥-prop (s 0))))
                     (isPropΠ (λ n → (isProp× (is⊥-prop x)
                                              (isProp→ {A = ℕ} (is⊥-prop (s (suc n))))))))
            (λ (p , f) → (p , λ _ → fst (f 1)) , λ m → p , (λ _ → snd (f 1) m))
            (λ ((p , f) , g) → p , (λ _ → (f 1) , (λ m → snd (g m) 1))) i
  is⊥ (isSet𝕊 x y p q i j) =
   fst (isSet→SquareP (λ _ _ → isSetHProp)
                      (λ j → is⊥ (p j) , is⊥-prop (p j))
                      (λ j → is⊥ (q j) , is⊥-prop (q j))
                      refl
                      refl i j)

  is⊥-prop : (x : 𝕊) → isProp (is⊥ x)
  is⊥-prop ⊤ = isProp⊥
  is⊥-prop ⊥ = isPropUnit
  is⊥-prop (⋁ s) = isProp× (is⊥-prop (s 0)) (isPropΠ (λ n → is⊥-prop (s (suc n))))
  is⊥-prop (∨-comm {x} {y} i) =
   isProp→PathP
     (λ i → isPropIsProp
              {A = hPropExt (isProp× (is⊥-prop x) (isProp→ {A = ℕ} (is⊥-prop y)))
                            (isProp× (is⊥-prop y) (isProp→ {A = ℕ} (is⊥-prop x)))
                            (λ (ix , f) → f 1 , λ _ → ix)
                            (λ (ix , f) → f 1 , λ _ → ix) i})
     (isProp× (is⊥-prop x) (isPropΠ {A = ℕ} (λ n → is⊥-prop y)))
     (isProp× (is⊥-prop y) (isPropΠ {A = ℕ} (λ n → is⊥-prop x))) i
  is⊥-prop (∨-assoc {x} {y} {z} i) =
   isProp→PathP
     (λ i → isPropIsProp
              {A = hPropExt (isProp× (is⊥-prop x)
                                     (isProp→ {A = ℕ}
                                       (isProp× (is⊥-prop y)
                                                (isProp→ {A = ℕ} (is⊥-prop z)))))
                            (isProp× (isProp× (is⊥-prop x)
                                              (isProp→ {A = ℕ} (is⊥-prop y)))
                                     (isProp→ {A = ℕ} (is⊥-prop z)))
                            (λ { (a , bc) → (a , λ _ → fst (bc 1)) , λ _ → snd (bc 1) 1 })
                            (λ ((a , b) , c) → a , λ _ → (b 1) , c) i})
     (isProp× (is⊥-prop x)
              (isPropΠ (λ n → isProp× (is⊥-prop y) (isPropΠ (λ n₁ → is⊥-prop z)))))
     (isProp× (isProp× (is⊥-prop x) (isPropΠ (λ n → is⊥-prop y)))
              (isPropΠ (λ n → is⊥-prop z))) i
  is⊥-prop (∨-idem {x} i) =
   isProp→PathP
     (λ i → isPropIsProp
              {A = (hPropExt (isProp× (is⊥-prop x) (isProp→ {A = ℕ} (is⊥-prop x)))
                             (is⊥-prop x)
                             fst
                             (λ p → p , (λ _ → p)) i)})
                (isProp× (is⊥-prop x) (isPropΠ (λ n → is⊥-prop x)))
                (is⊥-prop x) i
  is⊥-prop (∨-bot {x} i) =
   isProp→PathP
     (λ i → isPropIsProp
              {A = (hPropExt (isProp× (is⊥-prop x) (isProp→ {A = ℕ} isPropUnit))
                             (is⊥-prop x)
                             fst
                             (λ p → p , (λ _ → tt)) i)})
                (isProp× (is⊥-prop x) (isPropΠ (λ n → isPropUnit)))
                (is⊥-prop x) i
  is⊥-prop (∨-absorb {s = s} n i) =
   isProp→PathP
     (λ i → isPropIsProp
              {A = hPropExt (isProp× (is⊥-prop (s n))
                                     (isProp→ {A = ℕ}
                                       (isProp× (is⊥-prop (s 0))
                                                (isPropΠ {A = ℕ}
                                                  (λ m → is⊥-prop (s (suc m)))))))
                            (isProp× (is⊥-prop (s 0))
                                     (isPropΠ {A = ℕ} (λ m → (is⊥-prop (s (suc m))))))
                            (λ (sn , f) → (fst (f 1)) , (λ m → snd (f 1) m))
                            (λ (sz , f) → Nat.elim {A = λ n → is⊥ (s n)} sz (λ m _ → f m) n , λ m → sz , f) i})
    (isProp× (is⊥-prop (s n))
             (isPropΠ (λ n₁ → isProp× (is⊥-prop (s 0))
                                      (isPropΠ (λ m → is⊥-prop (s (suc m)))))))
    (isProp× (is⊥-prop (s 0)) (isPropΠ (λ n₁ → is⊥-prop (s (suc n₁))))) i
  is⊥-prop (∨-distr {s} {x} i) =
    isProp→PathP
      (λ i → isPropIsProp
               {A = hPropExt (isProp× (is⊥-prop x)
                                      (isProp→ {A = ℕ}
                                        (isProp× (is⊥-prop (s 0))
                                                 (isPropΠ {A = ℕ}
                                                   (λ m → (is⊥-prop (s (suc m))))))))
                             (isProp× (isProp× (is⊥-prop x)
                                               (isProp→ {A = ℕ} (is⊥-prop (s 0))))
                                      (isPropΠ
                                        (λ n → (isProp× (is⊥-prop x)
                                                        (isProp→ {A = ℕ}
                                                          (is⊥-prop (s (suc n))))))))
                             (λ (ix , f) → (ix , λ _ → fst (f 1)) , λ m → ix , (λ _ → snd (f 1) m))
                             (λ ((ix , f) , g) → ix , (λ _ → (f 1) , (λ m → snd (g m) 1))) i})
      (isProp× (is⊥-prop x)
               (isPropΠ (λ n → isProp× (is⊥-prop (s 0))
                                       (isPropΠ (λ n₁ → is⊥-prop (s (suc n₁)))))))
      (isProp× (isProp× (is⊥-prop x)
                        (isPropΠ (λ n → is⊥-prop (s 0))))
               (isPropΠ (λ n → isProp× (is⊥-prop x)
                                       (isPropΠ (λ n₁ → is⊥-prop (s (suc n))))))) i
  is⊥-prop (isSet𝕊 x y p q i j) =
   snd (isSet→SquareP (λ _ _ → isSetHProp)
                      (λ j → is⊥ (p j) , is⊥-prop (p j))
                      (λ j → is⊥ (q j) , is⊥-prop (q j))
                      refl
                      refl i j)

⊥≠⊤ : ⊥ ≡ ⊤ → Empty
⊥≠⊤ p = subst is⊥ p tt

is⊥-correct : ∀ {x} → is⊥ x → x ≡ ⊥
is⊥-correct {x} =
 𝕊-ind (λ x → is⊥ x → x ≡ ⊥) (λ x → isProp→ (isSet𝕊 x ⊥))
       Empty.rec
       (λ _ → refl)
       (λ {s} ih f → let s≡⊥ : s ≡ (λ n → ⊥)
                         s≡⊥ = funExt (λ { zero → ih 0 (fst f)
                                         ; (suc n) → ih (suc n) (snd f n) })
                     in subst (λ z → ⋁ z ≡ ⊥) (sym s≡⊥) ⋁-idem)
                 x

is⊥-correct⁻¹ : ∀ {x} → x ≡ ⊥ → is⊥ x
is⊥-correct⁻¹ {x} x≡⊥ = subst is⊥ (sym x≡⊥) tt

mutual
  is⊤ : 𝕊 -> Type ℓ-zero
  is⊤ ⊤ = Unit
  is⊤ ⊥ = Empty
  is⊤ (⋁ s) = ∥ (is⊤ (s 0)) ⊎ (Σ[ n ∈ ℕ ] is⊤ (s (suc n))) ∥
  is⊤ (∨-comm {x} {y} i) = hPropExt isPropPropTrunc
                                    isPropPropTrunc
                                    (∥-∥map (adjust x y))
                                    (∥-∥map (adjust y x))
                                    i
   module comm where
    adjust : (x y : 𝕊)
           → (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] is⊤ y) → (is⊤ y) ⊎ (Σ[ n ∈ ℕ ] is⊤ x)
    adjust x y (inl p) = inr (0 , p)
    adjust x y (inr (n , p)) = inl p
  is⊤ (∨-assoc {x} {y} {z} i) = hPropExt isPropPropTrunc
                                         isPropPropTrunc
                                         (∥-∥rec isPropPropTrunc adjust₁)
                                         (∥-∥rec isPropPropTrunc adjust₂)
                                         i
   module assoc where
    adjust₁ : (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ y) ⊎ (Σ[ m ∈ ℕ ] is⊤ z) ∥)
            → ∥ ∥ (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] is⊤ y) ∥ ⊎ (Σ[ m ∈ ℕ ] is⊤ z) ∥
    adjust₁ (inl p) = ∣ inl ∣ inl p ∣ ∣
    adjust₁ (inr (n , p)) = ∥-∥rec isPropPropTrunc (λ { (inl p) → ∣ inl ∣ inr ((1 , p)) ∣ ∣
                                                      ; (inr (m , p)) → ∣ inr ((1 , p)) ∣ }) p
    adjust₂ : ∥ (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] is⊤ y) ∥ ⊎ (Σ[ m ∈ ℕ ] is⊤ z)
            → ∥ (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ y) ⊎ (Σ[ m ∈ ℕ ] is⊤ z) ∥) ∥
    adjust₂ (inl p) = ∥-∥rec isPropPropTrunc (λ { (inl p) → ∣ inl p ∣
                                                ; (inr (m , p)) → ∣ inr (1 , ∣ inl p ∣) ∣ }) p
    adjust₂ (inr (n , p)) = ∣ inr (1 , ∣ inr ((1 , p)) ∣) ∣
  is⊤ (∨-idem {x} i) = hPropExt isPropPropTrunc
                                (is⊤-prop x)
                                (∥-∥rec (is⊤-prop x) adjust)
                                (λ p → ∣ inl p ∣) i
   module idem where
    adjust : (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] is⊤ x) → is⊤ x
    adjust (inl p) = p
    adjust (inr (n , p)) = p
  is⊤ (∨-bot {x} i) = hPropExt isPropPropTrunc
                               (is⊤-prop x)
                               (∥-∥rec (is⊤-prop x) adjust)
                               (λ p → ∣ inl p ∣) i
   module bot where
    adjust : (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] Empty) → is⊤ x
    adjust (inl p) = p
  is⊤ (∨-absorb {s} n i) = hPropExt isPropPropTrunc
                                    isPropPropTrunc
                                    (∥-∥rec isPropPropTrunc (adjust₁ n))
                                    (∥-∥rec isPropPropTrunc adjust₂) i
   module absorb where
    adjust₁ : (n : ℕ)
            → (is⊤ (s n)) ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ (s 0)) ⊎ (Σ[ m ∈ ℕ ] is⊤ (s (suc m))) ∥)
            → ∥ (is⊤ (s 0)) ⊎ (Σ[ n ∈ ℕ ] is⊤ (s (suc n))) ∥
    adjust₁ zero (inl p) = ∣ inl p ∣
    adjust₁ (suc n) (inl p) = ∣ inr (n , p) ∣
    adjust₁ n (inr (m , p)) = ∥-∥rec isPropPropTrunc ∣_∣ p
    adjust₂ : (is⊤ (s 0)) ⊎ (Σ[ n ∈ ℕ ] is⊤ (s (suc n)))
            → ∥ (is⊤ (s n)) ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ (s 0)) ⊎ (Σ[ m ∈ ℕ ] is⊤ (s (suc m))) ∥) ∥
    adjust₂ (inl p) = ∣ inr (1 , ∣ inl p ∣) ∣
    adjust₂ (inr p) = ∣ inr (1 , ∣ inr p ∣) ∣
  is⊤ (∨-distr {s} {x} i) = hPropExt isPropPropTrunc
                                     isPropPropTrunc
                                     (∥-∥rec isPropPropTrunc adjust₁)
                                     (∥-∥rec isPropPropTrunc adjust₂) i
   module distr where
    adjust₁ : (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ (s 0)) ⊎ (Σ[ m ∈ ℕ ] is⊤ (s (suc m)))∥)
            → ∥ ∥ (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] is⊤ (s 0)) ∥ ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ x) ⊎ (Σ[ m ∈ ℕ ] is⊤ (s (suc n))) ∥) ∥
    adjust₁ (inl p) = ∣ inl ∣ inl p ∣ ∣
    adjust₁ (inr (n , p)) =
     ∥-∥rec isPropPropTrunc (λ { (inl p) → ∣ inl ∣ inr (1 , p) ∣ ∣
                               ; (inr (m , p)) → ∣ inr (m , ∣ inr (1 , p) ∣) ∣ }) p
    adjust₂ : ∥ (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] is⊤ (s 0)) ∥ ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ x) ⊎ (Σ[ m ∈ ℕ ] is⊤ (s (suc n))) ∥)
            → ∥ (is⊤ x) ⊎ (Σ[ n ∈ ℕ ] ∥ (is⊤ (s 0)) ⊎ (Σ[ m ∈ ℕ ] is⊤ (s (suc m)))∥) ∥
    adjust₂ (inl p) = ∥-∥rec isPropPropTrunc (λ { (inl p) → ∣ inl p ∣
                                                ; (inr (m , p)) → ∣ inr (1 , ∣ inl p ∣) ∣ }) p
    adjust₂ (inr (n , p)) = ∥-∥rec isPropPropTrunc (λ { (inl p) → ∣ inl p ∣
                                                      ; (inr (m , p)) → ∣ inr (1 , ∣ inr (n , p) ∣) ∣ }) p
  is⊤ (isSet𝕊 x y p q i j) =
   fst (isSet→SquareP (λ _ _ → isSetHProp)
                      (λ j → is⊤ (p j) , is⊤-prop (p j))
                      (λ j → is⊤ (q j) , is⊤-prop (q j))
                      refl
                      refl i j)

  is⊤-prop : (x : 𝕊) → isProp (is⊤ x)
  is⊤-prop ⊤ = isPropUnit
  is⊤-prop ⊥ = isProp⊥
  is⊤-prop (⋁ s) = isPropPropTrunc
  is⊤-prop (∨-comm {x} {y} i) =
   isProp→PathP (λ i → isPropIsProp {A = hPropExt isPropPropTrunc
                                                  isPropPropTrunc
                                                  (∥-∥map (comm.adjust {x} {y} i x y))
                                                  (∥-∥map (comm.adjust {x} {y} i y x)) i})
                isPropPropTrunc
                isPropPropTrunc i
  is⊤-prop (∨-assoc {x} {y} {z} i) =
   isProp→PathP (λ i → isPropIsProp {A = hPropExt isPropPropTrunc
                                                  isPropPropTrunc
                                                  (∥-∥rec isPropPropTrunc (assoc.adjust₁ {x} {y} {z} i))
                                                  (∥-∥rec isPropPropTrunc (assoc.adjust₂ {x} {y} {z} i)) i})
                isPropPropTrunc
                isPropPropTrunc i

  is⊤-prop (∨-idem {x} i) =
   isProp→PathP (λ i → isPropIsProp {A = hPropExt isPropPropTrunc
                                                  (is⊤-prop x)
                                                  (∥-∥rec (is⊤-prop x) (idem.adjust {x} i))
                                                  (λ p → ∣ inl p ∣) i})
                isPropPropTrunc
                (is⊤-prop x) i
  is⊤-prop (∨-bot {x} i) =
   isProp→PathP (λ i → isPropIsProp {A = hPropExt isPropPropTrunc
                                                  (is⊤-prop x)
                                                  (∥-∥rec (is⊤-prop x) (bot.adjust {x} i))
                                                  (λ p → ∣ inl p ∣) i})
                isPropPropTrunc
                (is⊤-prop x) i
  is⊤-prop (∨-absorb {s} n i) =
   isProp→PathP (λ i → isPropIsProp {A = hPropExt isPropPropTrunc
                                                  isPropPropTrunc
                                                  (∥-∥rec isPropPropTrunc (absorb.adjust₁ {s} n i n))
                                                  (∥-∥rec isPropPropTrunc (absorb.adjust₂ {s} n i)) i})
                isPropPropTrunc
                isPropPropTrunc i
  is⊤-prop (∨-distr {s} {x} i) =
   isProp→PathP (λ i → isPropIsProp {A = hPropExt isPropPropTrunc
                                                  isPropPropTrunc
                                                  (∥-∥rec isPropPropTrunc (distr.adjust₁ {s} {x} i))
                                                  (∥-∥rec isPropPropTrunc (distr.adjust₂ {s} {x} i)) i})
                isPropPropTrunc
                isPropPropTrunc i
  is⊤-prop (isSet𝕊 x y p q i j) =
   snd (isSet→SquareP (λ _ _ → isSetHProp)
                      (λ j → is⊤ (p j) , is⊤-prop (p j))
                      (λ j → is⊤ (q j) , is⊤-prop (q j))
                      refl
                      refl i j)

is⊤-correct : ∀ {x} → is⊤ x → x ≡ ⊤
is⊤-correct {x} = 𝕊-ind (λ x → is⊤ x → x ≡ ⊤)
                                 (λ x → isProp→ (isSet𝕊 x ⊤))
                                 [1]
                                 [2]
                                 [3] x
 where
  [1] : is⊤ ⊤ → ⊤ ≡ ⊤
  [1] = λ _ → refl
  [2] : is⊤ ⊥ → ⊥ ≡ ⊤
  [2] = Empty.rec
  [3] : {s : ℕ → 𝕊}
      → ((n : ℕ) → is⊤ (s n) → s n ≡ ⊤)
      → ∥ is⊤ (s 0) ⊎ Σ-syntax ℕ (λ n → is⊤ (s (suc n))) ∥ → ⋁ s ≡ ⊤
  [3] {s} ih p = ∥-∥rec (isSet𝕊 (⋁ s) ⊤) [4] p
   where
    [4] : (is⊤ (s 0)) ⊎ (Σ[ n ∈ ℕ ] is⊤ (s (suc n))) → ⋁ s ≡ ⊤
    [4] (inl p) = contains-⊤-implies-is-⊤ s ∣ 0 , ih 0 p ∣
    [4] (inr (n , p)) = contains-⊤-implies-is-⊤ s ∣ suc n , ih (suc n) p ∣

is⊤-correct⁻¹ : ∀ {x} → x ≡ ⊤ → is⊤ x
is⊤-correct⁻¹ {x} x≡⊤ = subst (λ z → is⊤ z) (sym x≡⊤) tt

is-⊤-implies-contains-⊤ : (s : ℕ → 𝕊) -> ⋁ s ≡ ⊤ → ∃[ n ∈ ℕ ] s n ≡ ⊤
is-⊤-implies-contains-⊤ s ⋁s≡⊤ = ∥-∥rec isPropPropTrunc [1] (is⊤-correct⁻¹ ⋁s≡⊤)
 where
  [1] : is⊤ (s 0) ⊎ Σ-syntax ℕ (λ n → is⊤ (s (suc n))) → ∃[ n ∈ ℕ ] s n ≡ ⊤
  [1] (inl p) = ∣ 0 , is⊤-correct p ∣
  [1] (inr (n , p)) = ∣ suc n , is⊤-correct p ∣

is-⊤↔contains-⊤ : (s : ℕ → 𝕊) -> ⋁ s ≡ ⊤ ↔ ∃[ n ∈ ℕ ] s n ≡ ⊤
is-⊤↔contains-⊤ s = (is-⊤-implies-contains-⊤ s) , (contains-⊤-implies-is-⊤ s)

-- The order corresponding to least upper bounds ∨

_≼_ : 𝕊 → 𝕊 → Type
x ≼ y = (x ∨ y) ≡ y

isProp⟨≼⟩ : (x y : 𝕊) → isProp (x ≼ y)
isProp⟨≼⟩ x y = isSet𝕊 (x ∨ y) y

≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
≼-antisym {x} {y} x≼y y≼x = x ≡⟨ sym y≼x ⟩ y ∨ x ≡⟨ ∨-comm ⟩ x ∨ y ≡⟨ x≼y ⟩ y ∎

everything-under-⊤ : ∀ {x} → x ≼ ⊤
everything-under-⊤ = ⊤-is-top _

≼-refl : ∀ {x} → x ≼ x
≼-refl = ∨-idem

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans {x} {y} {z} x≼y y≼z =
  x ∨ z
    ≡⟨ cong (λ w → x ∨ w) (sym y≼z) ⟩
  (x ∨ (y ∨ z))
    ≡⟨ ∨-assoc ⟩
  ((x ∨ y) ∨ z)
    ≡⟨ cong (λ w → w ∨ z) x≼y ⟩
  (y ∨ z)
    ≡⟨ y≼z ⟩
  z ∎


_≼⟨_⟩_ : ∀ {y z} → (x : 𝕊) → (x ≼ y) → (y ≼ z) → (x ≼ z)
x ≼⟨ x≼y ⟩ y≼z = ≼-trans x≼y y≼z

_≼∎ : (x : 𝕊) → x ≼ x
_ ≼∎ = ≼-refl

infixr  0 _≼⟨_⟩_
infix   1 _≼∎

≼-cocone-simple : {s : ℕ → 𝕊} → ∀ k → s k ≼ ⋁ s
≼-cocone-simple = ∨-absorb

≼-cocone : {s : ℕ → 𝕊} {x : 𝕊} (k : ℕ) → x ≼ s k → x ≼ ⋁ s
≼-cocone {s} {x} k x≤sk = ≼-trans x≤sk (≼-cocone-simple k)

≼-limiting : (s : ℕ → 𝕊) {x : 𝕊} → ((k : ℕ) → s k ≼ x) → ⋁ s ≼ x
≼-limiting s {x} s≼x = ⋁ s ∨ x           ≡⟨ ∨-comm ⟩
                       x ∨ ⋁ s           ≡⟨ ∨-distr ⟩
                       ⋁ (λ k → x ∨ s k) ≡⟨ cong ⋁ (funExt λ k → ∨-comm) ⟩
                       ⋁ (λ k → s k ∨ x) ≡⟨ cong ⋁ (funExt λ k → s≼x k) ⟩
                       ⋁ (λ _ → x)       ≡⟨ ⋁-idem {x} ⟩
                       x                 ∎

⋁-on-≼ : {s s' : ℕ → 𝕊} → (∀ k → s k ≼ s' k) → ⋁ s ≼ ⋁ s'
⋁-on-≼ {s} {s'} l = ≼-limiting s (λ k → ≼-cocone {s'} k (l k))

⊥-minimal : ∀ {x} → ⊥ ≼ x
⊥-minimal {x} =
 𝕊-ind (λ x → ⊥ ≼ x)
       (λ x → isSet𝕊 _ _)
       everything-under-⊤
       ≼-refl
       ((λ {s} ih → ≼-cocone {s} 1 (ih 1)))
       x

-- 𝕊-decidability

𝕊-dec : Type ℓ → Type ℓ
𝕊-dec P = Σ[ x ∈ 𝕊 ] (P ↔ x ≡ ⊤)

⌊_⌋ : {P : Type ℓ} → 𝕊-dec P → 𝕊
⌊ x , p ⌋ = x

⌊_⌋-correct : {P : Type ℓ} → (s : 𝕊-dec P) → (P ↔ ⌊ s ⌋ ≡ ⊤)
⌊ x , p ⌋-correct = p

𝕊-dec-stable-under-↔ : {P : Type ℓ}{Q : Type ℓ'}
                     → (P ↔ Q)
                     → 𝕊-dec P ↔ 𝕊-dec Q
𝕊-dec-stable-under-↔ r =
 (λ (x , ρ) → (x , ↔-trans (↔-sym r) ρ)) , (λ (x , ρ) → (x , ↔-trans r ρ))

Dec→𝕊-dec : {P : Type ℓ} → Dec P → 𝕊-dec P
Dec→𝕊-dec (yes p) = ⊤ , ((λ _ → refl) , λ _ → p)
Dec→𝕊-dec (no ¬p) = ⊥ , ((λ p → Empty.rec (¬p p)) , λ ⊥≡⊤ → Empty.rec (⊥≠⊤ ⊥≡⊤))

eq𝕊-dec : {P : Type ℓ} → isProp P → {u v : 𝕊-dec P} → fst u ≡ fst v → u ≡ v
eq𝕊-dec {P = P} isProp⟨P⟩ {x , p↔x≡⊤} {y , p↔y≡⊤} x≡y =
  Σ≡Prop {B = λ x → (P → x ≡ ⊤) × (x ≡ ⊤ → P)}
         (λ x → isProp× (isPropΠ λ _ → isSet𝕊 x ⊤) (isPropΠ λ _ → isProp⟨P⟩))
         {u = x , p↔x≡⊤}
         {v = y , p↔y≡⊤}
         x≡y

not-⊤-is-⊥ : ∀ y → (y ≡ ⊤ → Empty) → y ≡ ⊥
not-⊤-is-⊥ =
 𝕊-ind (λ y → (y ≡ ⊤ → Empty) → y ≡ ⊥)
       (λ x → isProp→ (isSet𝕊 x ⊥))
       (λ p → Empty.rec (p refl))
       (λ _ → refl)
       (λ {s} ih q → is⊥-correct {⋁ s}
                      (is⊥-correct⁻¹ (ih 0 ([1] s q 0)) ,
                       λ n → is⊥-correct⁻¹ (ih (suc n) ([1] s q (suc n)))))
  where
  [1] :  (s : ℕ → 𝕊) -> (⋁ s ≡ ⊤ → Empty) → (n : ℕ) → s n ≡ ⊤ → Empty
  [1] s p n sn≡⊤ = p (contains-⊤-implies-is-⊤ s ∣ n , sn≡⊤ ∣)

bisimilar-implies-⋁-equal : {s s' : ℕ → 𝕊}
                          → ((n : ℕ) → ∃[ m ∈ ℕ ] s' n ≼ s m)
                          → ((n : ℕ) → ∃[ m ∈ ℕ ] s n ≼ s' m)
                          → ⋁ s ≡ ⋁ s'
bisimilar-implies-⋁-equal {s} {s'} p q =
 ≼-antisym
  (≼-limiting s {⋁ s'} (λ k → ∥-∥rec (isSet𝕊 _ _)
                                     (λ (l , sk≼s'l) → ≼-cocone {s'} {s k} l sk≼s'l) (q k)))
  (≼-limiting s' {⋁ s} (λ k → ∥-∥rec (isSet𝕊 _ _)
                                     (λ (l , s'k≼sl) → ≼-cocone {s} {s' k} l s'k≼sl) (p k)))

⋁-equal-implies-bisimilar-≡⟙ : {s s' : ℕ → 𝕊}
                             → ⋁ s ≡ ⋁ s'
                             → ((n : ℕ) → s n ≡ ⊤ → ∃[ m ∈ ℕ ] s' m ≡ ⊤)
                             × ((n : ℕ) → s' n ≡ ⊤ → ∃[ m ∈ ℕ ] s m ≡ ⊤)
⋁-equal-implies-bisimilar-≡⟙ {s} {s'} ⋁s≡⋁s' =
 (⋁-equal-implies-simulation ⋁s≡⋁s' , ⋁-equal-implies-simulation (sym ⋁s≡⋁s'))
  where
   ⋁-equal-implies-simulation : {s s' : ℕ → 𝕊}
                              → ⋁ s ≡ ⋁ s'
                              → (n : ℕ) → s n ≡ ⊤ → ∃[ m ∈ ℕ ] s' m ≡ ⊤
   ⋁-equal-implies-simulation {s} {s'} e n q =
    is-⊤-implies-contains-⊤ s' (sym (subst (_≡ ⋁ s')
                                           (contains-⊤-implies-is-⊤ s ∣ n , q ∣) e))

≼-if-preserves-≡⟙ : (x y : 𝕊) → (x ≡ ⊤ → y ≡ ⊤) → x ≼ y
≼-if-preserves-≡⟙ = 𝕊-ind (λ x → ∀ y → (x ≡ ⊤ → y ≡ ⊤) → x ≼ y)
                          (λ x → isPropΠ (λ y → isProp→ (isProp⟨≼⟩ x y)))
                          [1]
                          [2]
                          [3]
 where
  [1] : (y : 𝕊) → (⊤ ≡ ⊤ → y ≡ ⊤) → ⊤ ≼ y
  [1] y p = subst (⊤ ≼_) (sym (p refl)) ≼-refl

  [2] : (y : 𝕊) → (⊥ ≡ ⊤ → y ≡ ⊤) → ⊥ ≼ y
  [2] y p = ⊥-minimal {y}

  [3] : {s : ℕ → 𝕊}
      → ((n : ℕ) (y : 𝕊) → (s n ≡ ⊤ → y ≡ ⊤) → s n ≼ y)
      → (y : 𝕊) → (⋁ s ≡ ⊤ → y ≡ ⊤) → ⋁ s ≼ y
  [3] {s} ih y p =
   ≼-limiting s (λ k → ih k y (λ sk≡⊤ → p (contains-⊤-implies-is-⊤ s ∣ k , sk≡⊤ ∣)))

eq𝕊 : (x y : 𝕊) -> (x ≡ ⊤ → y ≡ ⊤) → (y ≡ ⊤ → x ≡ ⊤) → x ≡ y
eq𝕊 x y p q = ≼-antisym (≼-if-preserves-≡⟙ x y p) (≼-if-preserves-≡⟙ y x q)

isProp𝕊Dec : {P : Type ℓ} → isProp P → isProp (𝕊-dec P)
isProp𝕊Dec {P = P} isProp⟨P⟩ (x , p↔x≡⊤) (y , p↔y≡⊤) =
 eq𝕊-dec isProp⟨P⟩ (eq𝕊 x y x≡⊤ y≡⊤)
  where
   x≡⊤ : x ≡ ⊤ → y ≡ ⊤
   x≡⊤ = λ x≡⊤ → fst p↔y≡⊤ (snd p↔x≡⊤ x≡⊤)
   y≡⊤ : y ≡ ⊤ → x ≡ ⊤
   y≡⊤ = λ y≡⊤ → fst p↔x≡⊤ (snd p↔y≡⊤ y≡⊤)

𝕊-decOr : {P : Type ℓ}{Q : Type ℓ'}
                 → 𝕊-dec P
                 → 𝕊-dec Q
                 → 𝕊-dec (∥ P ⊎ Q ∥)
𝕊-decOr (sp , lp , rp) (sq , lq , rq) =
 (sp ∨ sq ,
 (∥-∥rec (isSet𝕊 _ _) (λ { (inl p) → contains-⊤-implies-is-⊤ _ ∣ 0 , lp p ∣
                         ; (inr q) → contains-⊤-implies-is-⊤ _ ∣ 1 , lq q ∣ })) ,
  λ w → ∥-∥rec isPropPropTrunc (λ { (zero , x) → ∣ inl (rp x) ∣
                                  ; (suc n , x) → ∣ inr (rq x) ∣ })
                               (is-⊤-implies-contains-⊤ _ w))

𝟚→𝕊 : Bool → 𝕊
𝟚→𝕊 false = ⊥
𝟚→𝕊 true = ⊤

𝟚→𝕊-⊤-from-true : {b : Bool} → 𝟚→𝕊 b ≡ ⊤ → b ≡ true
𝟚→𝕊-⊤-from-true {false} e = Empty.rec (⊥≠⊤ e)
𝟚→𝕊-⊤-from-true {true} e = refl

semidec→𝕊-dec : (P : Type ℓ) → isProp P → semi-dec P → 𝕊-dec P
semidec→𝕊-dec P is-prop-P = ∥-∥rec (isProp𝕊Dec is-prop-P) δ
 where
  δ : semi-dec-str P → 𝕊-dec P
  δ (s , l , r) = ⋁ (λ n → 𝟚→𝕊 (s n)) , l' , r'
   where
    l' : P → ⋁ (λ n → 𝟚→𝕊 (s n)) ≡ ⊤
    l' p = contains-⊤-implies-is-⊤ (λ n → (𝟚→𝕊 (s n)))
                                   (∥-∥map (λ (n , e) → n , cong 𝟚→𝕊 e) (l p))

    r' : ⋁ (λ n → 𝟚→𝕊 (s n)) ≡ ⊤ → P
    r' e = r (∥-∥map (λ (n , e) → n , 𝟚→𝕊-⊤-from-true e)
                     (is-⊤-implies-contains-⊤ _ e))

dec→𝕊-dec : (P : Type ℓ) → Dec P → 𝕊-dec P
dec→𝕊-dec P (yes p) = ⊤ , ((λ _ → refl) , (λ _ → p))
dec→𝕊-dec P (no ¬p) = ⊥ , ((λ p → Empty.rec (¬p p)) , λ q → Empty.rec (⊥≠⊤ q))
