----------------------------------------------------------------------------------------------------
-- Some general properties for the development
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --safe --guardedness #-}

module General-Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Bool as Bool hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order as Nat using (_<_; _≤_; lt; eq; gt; ≤-refl)
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_; Dec→Stable)
open import Cubical.Relation.Binary
open BinaryRelation
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)

open import Iff
open import PropTrunc

private
 variable
  ℓ ℓ' : Level

least-witness : (P : ℕ → Type ℓ) → (∀ n → isProp (P n)) → (∀ n → Dec (P n))
              → ∃ ℕ P → Σ ℕ P
least-witness {ℓ} P propP decP witness = goal
 where
  least-P : ℕ → Type ℓ
  least-P n = P n × ((m : ℕ) → m < n → ¬ (P m))

  project : Σ ℕ least-P → Σ ℕ P
  project (n , (p , _)) = (n , p)

  isProp⟨Σleast-P⟩ : isProp (Σ ℕ least-P)
  isProp⟨Σleast-P⟩ (m , m-min) (n , n-min) = Σ≡Prop (λ k → isProp× (propP k)
                                                    (isPropΠ3 λ _ _ _ → isProp⊥)) lemma
   where
    lemma : m ≡ n
    lemma with m Nat.≟ n
    ... | lt m<n = ⊥.rec (snd n-min m m<n (fst m-min))
    ... | eq m=n = m=n
    ... | gt m>n = ⊥.rec (snd m-min n m>n (fst n-min))

  boundedSearch-aux : (n k : ℕ) → P n → Σ ℕ least-P ⊎ ((m : ℕ) → m ≤ k → ¬ (P m))
  boundedSearch-aux n zero pn with decP zero
  ... | yes p = inl (zero , (p , (λ m (k , r) → ⊥.rec (snotz (sym (+-suc k m) ∙ r)))))
  ... | no ¬p = inr λ { m (k , r) → subst (λ z → ¬ (P z)) (sym (snd (m+n≡0→m≡0×n≡0 r))) ¬p }
  boundedSearch-aux n (suc k) pn with boundedSearch-aux n k pn
  ... | inl x = inl x
  ... | inr x with decP (suc k)
  ... | yes p = inl (suc k , p , (λ { m (k , r) → x m ((k , injSuc (sym (+-suc k m) ∙ r))) }))
  ... | no ¬p = inr f where
    f : (m : ℕ) → m ≤ suc k → ¬ (P m)
    f m (zero , r) = subst (λ z → ¬ (P z)) (sym r) ¬p
    f m (suc k , r) = x m (k , injSuc r)

  boundedSearch : (n : ℕ) → P n → Σ ℕ least-P
  boundedSearch n pn with boundedSearch-aux n n pn
  ... | inl x = x
  ... | inr x = ⊥.rec (x n ≤-refl pn)

  goal : Σ ℕ P
  goal = project (∥-∥rec isProp⟨Σleast-P⟩ (λ (n , p) → boundedSearch n p) witness)

{- A *truncated relation* is a set `A` and a relation `A → A → Set`
   that is valued in propositions. -}

isTruncatedRelation : {A : Type ℓ} → (_<_ : A → A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isTruncatedRelation {A = A} _<_ = isSet A × isPropValued _<_

{- Extensionality -}

isExtensional : {A : Type ℓ} -> (_<_ : A -> A -> Type ℓ') -> Type (ℓ-max ℓ ℓ')
isExtensional {A = A} _<_ = (a b : A) → ((c : A) → (c < a ↔ c < b)) → a ≡ b

{- Law of excluded middle -}

LEM : Type₁
LEM = (P : Type) -> isProp P -> Dec P

LEM-¬∀-∃ : ∀ {A : Set} (P : A -> Set) -> LEM -> ¬ ((x : A) -> ¬ P x) -> ∥ Σ A P ∥
LEM-¬∀-∃ {A} P lem P-impossible with lem (∥ Σ A P ∥) squash
... | yes p = p
... | no ¬a,p = ⊥.elim (P-impossible λ a → λ p → ¬a,p ∣ a , p ∣)

DNE : Type₁
DNE = (P : Type) → isProp P → ¬ (¬ P) → P

LEM-to-DNE : LEM → DNE
LEM-to-DNE lem P pP ¬¬p with (lem P pP)
... | yes p = p
... | no ¬p = ⊥.elim (¬¬p ¬p)

LEM-¬∀-∃¬ : ∀ {A : Type} (P : A → Type) → (∀ a → isProp (P a)) →
            LEM → ¬ (∀ x → P x) → ∥ Σ A (\x → ¬ P x) ∥
LEM-¬∀-∃¬ {A} P pvP lem f = LEM-¬∀-∃ _ lem g
 where
  g : ¬ (∀ x → ¬ (¬ P x))
  g h = f (λ x → LEM-to-DNE lem (P x) (pvP x) (h x))

WLPO : Type
WLPO = (s : ℕ → Bool) → (∀ k → s k ≡ false) ⊎ (¬ (∀ k → s k ≡ false))

LPO : Type
LPO = (s : ℕ → Bool) → (∀ k → s k ≡ false) ⊎ ∥ Σ[ n ∈ ℕ ] (s n ≡ true) ∥

Σ-LPO : Type
Σ-LPO = (s : ℕ → Bool) → (∀ k → s k ≡ false) ⊎ (Σ[ n ∈ ℕ ] (s n ≡ true))

LPO-to-Σ-LPO : LPO → Σ-LPO
LPO-to-Σ-LPO lpo s with lpo s
... | inl x = inl x
... | inr x = inr (least-witness (λ n → s n ≡ true)
                                 (λ n → isSetBool (s n) true)
                                 (λ n → Bool._≟_ (s n) true) x)

Σ-LPO-to-LPO : Σ-LPO → LPO
Σ-LPO-to-LPO Σ-lpo s with Σ-lpo s
... | inl x = inl x
... | inr x = inr ∣ x ∣

-- Markov's principle

MP : Type
MP = (s : ℕ → Bool) → ¬ (¬ (Σ[ n ∈ ℕ ] (s n ≡ true))) → Σ[ n ∈ ℕ ] (s n ≡ true)

-- Note: no difference between formulation using Σ or ∃

-- LPO ↔ WLPO × MP

LPO→MP : LPO → MP
LPO→MP lpo s ¬¬p with LPO-to-Σ-LPO lpo s
... | inl all-false = ⊥.rec (¬¬p λ { (n , sn≡true) → true≢false ((sym sn≡true) ∙ all-false n ) })
... | inr one-true = one-true

LPO→WLPO : LPO → WLPO
LPO→WLPO lpo s = map (λ x → x) (λ { (n , p) → λ q → true≢false (sym p ∙ q n) }) (LPO-to-Σ-LPO lpo s)

WLPO×MP→LPO : WLPO → MP → LPO
WLPO×MP→LPO wlpo mp s =
  map (λ x → x)
      (λ p → ∣ mp s (λ q → p (λ k → Dec→Stable (s k ≟ false)
                                               (λ sk≠false → q (k , (¬false→true _ sk≠false))))) ∣)
      (wlpo s)

-- Countable Choice

CountableChoice : (ℓ : Level) → Type (ℓ-suc ℓ)
CountableChoice ℓ = {A : ℕ → Type ℓ}
                  → (∀ (k : ℕ) →  ∥ A k ∥)
                  → ∥ (∀ (k : ℕ) → (A k)) ∥

CC-lower : CountableChoice ℓ → CountableChoice ℓ-zero
CC-lower {ℓ = ℓ} cc {A} f = ∥-∥map τ (cc {λ n → Lift (A n)} f')
 where
  τ : ((k : ℕ) → Lift (A k)) → (k : ℕ) → A k
  τ a k = lower (a k)
  f' : (k : ℕ) → ∥ Lift (A k) ∥
  f' k = ∥-∥map lift (f k)

{- Wellfoundedness iff transfinite induction holds. -}

wellfounded→TI : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'} →
                 isWellFounded _<_ →
                 (∀ {ℓ''}{P : A → Type ℓ''} → ((x : A) → ((y : A) → y < x → P y) → P x) → (x : A) → P x)
wellfounded→TI = WFI.induction

TI→wellfounded : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'} →
                 (∀ {ℓ''}{P : A → Type ℓ''} → ((x : A) → ((y : A) → y < x → P y) → P x) → (x : A) → P x) →
                 isWellFounded _<_
TI→wellfounded {A = A} {_<_} TI = TI {P = Acc _<_} (λ x → acc {x = x})

{- Wellfoundedness implies that there is no infinite descending sequence. -}

no-infinite-descending-sequence : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'}
                                → isWellFounded _<_
                                → ¬ (Σ[ f ∈ (ℕ → A) ] (∀ i → f (suc i) < f i))
no-infinite-descending-sequence {_} {_} {A} {_<_} wf (f , inf-desc) =
  WFI.induction wf {P = P} step (f 0) (f , refl , inf-desc)
  where
    P : A → Type _
    P a = ¬ (Σ[ f ∈ (ℕ → A) ] (f 0 ≡ a) × (∀ i → f (suc i) < f i))
    step : (x : A) → ((y : A) → y < x → P y) → P x
    step x q (f , f0≡x , inf-desc-f) =
      q (f 1) (subst (f 1 <_) f0≡x (inf-desc-f 0))
              (f ∘ suc , refl , λ i → inf-desc-f (suc i))

{- Wellfoundedness implies irreflexivity. -}

wellfounded→irreflexive : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'}
                        → isWellFounded _<_ → isIrrefl _<_
wellfounded→irreflexive is-wf x x<x = no-infinite-descending-sequence is-wf ((λ n → x) , λ n → x<x)

irreflexive-≡→reflexive-closure-is-prop :
    ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'}
  → isSet A → isPropValued _<_
  → (∀{x y} → x ≡ y → ¬ (x < y))
  → ∀ {x y} → isProp ((x < y) ⊎ (x ≡ y))
irreflexive-≡→reflexive-closure-is-prop is-set is-pv irrefl (inl p) (inl p') =
  cong inl (is-pv _ _ p p')
irreflexive-≡→reflexive-closure-is-prop is-set is-pv irrefl (inl p) (inr q') =
  ⊥.rec (irrefl q' p)
irreflexive-≡→reflexive-closure-is-prop is-set is-pv irrefl (inr q) (inl p') =
  ⊥.rec (irrefl q p')
irreflexive-≡→reflexive-closure-is-prop is-set is-pv irrefl (inr q) (inr q') =
  cong inr (is-set _ _ q q')

irreflexive→reflexive-closure-is-prop :
    ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'}
  → isSet A → isPropValued _<_
  → isIrrefl _<_
  → ∀ {x y} → isProp ((x < y) ⊎ (x ≡ y))
irreflexive→reflexive-closure-is-prop {_} {_} {A} {_<_} is-set is-pv irrefl =
  irreflexive-≡→reflexive-closure-is-prop is-set is-pv (λ p → subst (λ z → ¬ (_ < z)) p (irrefl _))

wellfounded→reflexive-closure-is-prop :
    ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'}
  → isSet A → isPropValued _<_
  → isWellFounded _<_
  → ∀ {x y} → isProp ((x < y) ⊎ (x ≡ y))
wellfounded→reflexive-closure-is-prop is-set is-pv is-wf =
  irreflexive→reflexive-closure-is-prop is-set is-pv (wellfounded→irreflexive is-wf)

isTrichotomous : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → A → Type ℓ') → Type _
isTrichotomous _<_ = ∀ x y → (x < y) ⊎ ((y < x) ⊎ (x ≡ y))

isConnex : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → A → Type ℓ') → Type _
isConnex _≤_ = ∀ x y → (x ≤ y) ⊎ (y ≤ x)

Splits : ∀ {ℓ ℓ'} (A : Type ℓ) → (< ≤ : A → A → Type ℓ') → Type _
Splits A _<_ _≤_ = {x y : A} → x ≤ y → (x < y) ⊎ (x ≡ y)

trichotomous→Splits-≤ : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ _≤_ : A → A → Type ℓ'} →
                        isIrrefl _<_ →
                        (<∘≤-in-< : {a b c : A} → a < b → b ≤ c → a < c) →
                        isTrichotomous _<_ → Splits A _<_ _≤_
trichotomous→Splits-≤ irrefl <∘≤-in-< tri {x} {y} x≤y with tri x y
... | inl      x<y  = inl x<y
... | inr (inl y<x) = ⊥.rec (irrefl y (<∘≤-in-< y<x x≤y))
... | inr (inr x=y) = inr x=y

<∘≤-in-<→Splits-≤ : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ _≤_ : A → A → Type ℓ'}
                  → isIrrefl _<_ → isTrichotomous _<_
                  → (<∘≤-in-< : {a b c : A} → a < b → b ≤ c → a < c)
                  → Splits A _<_ _≤_
<∘≤-in-<→Splits-≤ irrefl tri <∘≤-in-< {x} {y} x≤y with tri x y
... | inl      x<y  = inl x<y
... | inr (inl y<x) = ⊥.rec (irrefl y (<∘≤-in-< y<x x≤y))
... | inr (inr x=y) = inr x=y

Splits-≤→<∘≤-in-< : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ _≤_ : A → A → Type ℓ'}
                  → isTrans _<_
                  → Splits A _<_ _≤_
                  → {a b c : A} → a < b → b ≤ c → a < c
Splits-≤→<∘≤-in-< {_<_ = _<_} trans splits a<b b≤c with splits b≤c
... | inl b<c = trans _ _ _ a<b b<c
... | inr b=c = subst (_ <_) b=c a<b

isAssoc : ∀ {ℓ} {A : Type ℓ} → (A → A → A) → Type ℓ
isAssoc _⋆_ = ∀ x y z → (x ⋆ (y ⋆ z)) ≡ ((x ⋆ y) ⋆ z)

isPropLift : ∀ {ℓ ℓ'} → {A : Type ℓ} → isProp A → isProp (Lift {j = ℓ'} A)
isPropLift A-prop (lift x) (lift y) = cong lift (A-prop x y)
