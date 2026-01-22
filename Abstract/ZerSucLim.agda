----------------------------------------------------------------------------------------------------
-- An axiomatic approach to ordinals
----------------------------------------------------------------------------------------------------

{- A set `A` with relations `<` and `≤` satisfying certain conditions
   allow us to define standard concepts of ordinals. This means that
   we treat `A` as some sort of "abstract ordinal". -}

{-# OPTIONS --cubical --erasure --safe --guardedness  #-}

open import Cubical.Foundations.Prelude

module Abstract.ZerSucLim
  {i j k}
  {A : Type i}
  (_<_ : A → A → Type j)
  (_≤_ : A → A → Type k)
  where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Bool renaming (true to tt; false to ff) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order as N using ()
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary using (¬_; Discrete; yes; no)
open import Cubical.Relation.Binary
open BinaryRelation
  renaming (isTrans to isTransitive ; isRefl to isReflexive)
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded; Acc to isAcc)

open import Iff
open import PropTrunc
open import General-Properties
open import BooleanSequence

-- open import Relation.Binary.PropositionalEquality using (inspect)

{- monotonicity definition -}

is-<-monotone : (f : A → A) → Type _
is-<-monotone f = {b a : A} → b < a → f b < f a

is-≤-monotone : (f : A → A) → Type _
is-≤-monotone f = {b a : A} → b ≤ a → f b ≤ f a

is-pointwise-≤-monotone : ((ℕ → A) → A) → Type _
is-pointwise-≤-monotone ⊔ = (f g : ℕ → A) → (∀ n → f n ≤ g n) → ⊔ f ≤ ⊔ g

{- increasing definition -}

is-<-increasing : (ℕ → A) → Type _
is-<-increasing f = ∀ k → f k < f (suc k)

is-≤-increasing : (ℕ → A) → Type _
is-≤-increasing f = ∀ k → f k ≤ f (suc k)

{- Zero -}

is-zero : A → Type _
is-zero a = (b : A) → a ≤ b

Zer : Type _
Zer = Σ[ a ∈ A ] (is-zero a)

has-zero : Type _
has-zero = Zer

{- Successor -}

_is-suc-of_ : A → A → Type _
a is-suc-of b = (b < a) × (∀ x → b < x → a ≤ x)

calc-suc : (s : A → A) → Type _
calc-suc s = (b : A) → (s b) is-suc-of b

has-suc : Type _
has-suc = Σ[ s ∈ (A → A) ] calc-suc s

is-suc : A → Type _
is-suc a = ∥ Σ[ b ∈ A ] a is-suc-of b ∥

{- Predecessor and strong successor -}
-- (predecessor is not used, but the strong successor is central)

_is-pred-of_ : A → A → Type _
b is-pred-of a = (b < a) × (∀ x → x < a → x ≤ b)

_is-strong-suc-of_ : A → A → Type _
a is-strong-suc-of b = a is-suc-of b × ∀ x → x < a → x ≤ b

is-strong-suc : A → Type _
is-strong-suc a = Σ[ b ∈ A ] a is-strong-suc-of b

calc-strong-suc : (s : A → A) → Type _
calc-strong-suc s = (b : A) → (s b) is-strong-suc-of b

has-strong-suc : Type _
has-strong-suc = Σ[ s ∈ (A → A) ] calc-strong-suc s

{- Supremum -}

_is-_-sup-of_ : ∀ {ℓ} → A → (X : Type ℓ) → (X → A) → Type _
a is- X -sup-of f = (∀ i → f i ≤ a) × (∀ x → ((∀ i → f i ≤ x) → a ≤ x))

_is-sup-of_ : A → (ℕ → A) → Type _
a is-sup-of f = a is- ℕ -sup-of f

calc-sup : ((ℕ → A) → A) → Type _
calc-sup ⊔ = ∀ f → (⊔ f) is-sup-of f

has-sup : Type _
has-sup = Σ[ ⊔ ∈ ((ℕ → A) → A) ] calc-sup ⊔

-- Remark: other definition of supremum (not used)
_is-sup∃-of_ : A → (ℕ → A) → Type _
a is-sup∃-of f = (∀ i → f i ≤ a) × (∀ x → (x < a → ∃[ i ∈ ℕ ] x ≤ f i))

{- Binary join -}

_is-join-of_and_ : A → A → A → Type _
a is-join-of b and c = (b ≤ a × c ≤ a) × (∀ x → b ≤ x → c ≤ x → a ≤ x)

calc-join : (A → A → A) → Type _
calc-join _⊔_ = ∀ b c → (b ⊔ c) is-join-of b and c

has-join : Type _
has-join = Σ[ _⊔_ ∈ (A → A → A) ] (calc-join _⊔_)

{- Limits -}

IncrSeq : Type _
IncrSeq = Σ[ f ∈ (ℕ → A) ] is-<-increasing f

IncrBoundedSeq : Type _
IncrBoundedSeq = Σ[ f ∈ (ℕ → A) ] (is-<-increasing f × (Σ[ b ∈ A ] (∀ k → f k < b)))

_is-lim-of_ : A → IncrSeq → Type _
a is-lim-of (f , _) = a is-sup-of f

is-Σlim : A → Type _
is-Σlim a = Σ[ f ∈ IncrSeq ] a is-lim-of f

is-lim : A → Type _
is-lim a = ∥ is-Σlim a ∥

is-general-lim : A → Type _
is-general-lim a = ∥ Σ A (λ z → z < a) ∥ × (a is- Σ A (_< a) -sup-of fst)

has-limits : Type _
has-limits = Σ[ lim ∈ (IncrSeq → A) ] ∀ f → lim f is-lim-of f

has-limits-of-bounded-sequences : Type _
has-limits-of-bounded-sequences = Σ[ lim ∈ (IncrBoundedSeq → A) ] ∀ f → lim f is-sup-of (fst f)

{- Classifiability -}

is-classifiable : A → Type _
is-classifiable a = is-zero a ⊎ (is-strong-suc a ⊎ is-lim a)

is-weakly-classifiable : A → Type _
is-weakly-classifiable a = is-zero a ⊎ (is-strong-suc a ⊎ is-general-lim a)

is-Σclassifiable : A → Type _
is-Σclassifiable a = is-zero a ⊎ (is-strong-suc a ⊎ is-Σlim a)

to-is-classifiable : {a : A} → is-Σclassifiable a → is-classifiable a
to-is-classifiable (inl x) = inl x
to-is-classifiable (inr (inl x)) = inr (inl x)
to-is-classifiable (inr (inr x)) = inr (inr ∣ x ∣)

not-zs-is-lim : {a : A} → is-Σclassifiable a
              → ¬ (is-zero a) → ¬ (is-strong-suc a) → is-Σlim a
not-zs-is-lim (inl x)       f g = ⊥.rec (f x)
not-zs-is-lim (inr (inl x)) f g = ⊥.rec (g x)
not-zs-is-lim (inr (inr x)) f g = x

-- We say that (A , < , ≤) is classifiable if every `a : A` is.
has-classification : Type _
has-classification = (a : A) → is-classifiable a

has-weak-classification : Type _
has-weak-classification = (a : A) → is-weakly-classifiable a

satisfies-classifiability-induction : ∀ ℓ → Type _
satisfies-classifiability-induction ℓ =
  ∀ {P : A → Type ℓ}
 → (∀ a → isProp (P a))
 → (∀ a → is-zero a → P a)
 → (∀ a b → a is-strong-suc-of b → P b → P a)
 → (∀ a f f↑ → a is-lim-of (f , f↑) → (∀ i → P (f i)) → P a)
 → ∀ a → P a

isProp⟨is-join-of⟩ : (∀ {a b} → isProp (a ≤ b)) → ∀ {a b c} → isProp (a is-join-of b and c)
isProp⟨is-join-of⟩ isProp⟨≤⟩ = isProp× (isProp× isProp⟨≤⟩ isProp⟨≤⟩) (isPropΠ3 λ y _ _ → isProp⟨≤⟩)


module Properties
  (A-is-set : isSet A)
  (isProp⟨<⟩ : isPropValued _<_)
  (isProp⟨≤⟩ : isPropValued _≤_)
  (<-irrefl : isIrrefl _<_)
  (≤-refl : isReflexive _≤_)
  (≤-trans : isTransitive _≤_)
  (≤-antisym : isAntisym _≤_)
  (<-in-≤ : {a b : A} → a < b → a ≤ b)
  (<∘≤-in-< : {a b c : A} → a < b → b ≤ c → a < c)
  where

  private
    ≤-reflexive : {a b : A} → a ≡ b → a ≤ b
    ≤-reflexive {a} {b} p = subst (a ≤_) p (≤-refl a)

  ≮-zero : ∀ {a} → is-zero a → (b : A) → ¬ (b < a)
  ≮-zero {a} isz b b<a = <-irrefl b (<∘≤-in-< b<a (isz b))

  isProp⟨is-zero⟩ : (a : A) → isProp (is-zero a)
  isProp⟨is-zero⟩ a = isPropΠ λ _ → isProp⟨≤⟩ _ _

  isProp⟨Zer⟩ : isProp Zer
  isProp⟨Zer⟩ (a₁ , p₁) (a₂ , p₂) = Σ≡Prop isProp⟨is-zero⟩ (≤-antisym _ _ (p₁ a₂) (p₂ a₁))

  isProp⟨is-suc-of⟩ : {a b : A} → isProp (a is-suc-of b)
  isProp⟨is-suc-of⟩ =
    isProp× (isProp⟨<⟩ _ _)
            (isPropΠ λ _ → isPropΠ λ _ → isProp⟨≤⟩ _ _)

  isProp⟨calc-suc⟩ : (s : A → A) → isProp (calc-suc s)
  isProp⟨calc-suc⟩ s = isPropΠ λ _ → isProp⟨is-suc-of⟩

  suc-unique : (b : A) → isProp (Σ[ a ∈ A ] (a is-suc-of b))
  suc-unique b (a₁ , b<a₁ , a₁-min) (a₂ , b<a₂ , a₂-min) =
    Σ≡Prop (λ _ → isProp⟨is-suc-of⟩) (≤-antisym _ _ (a₁-min a₂ b<a₂) (a₂-min a₁ b<a₁))

  isProp⟨has-suc⟩ : isProp has-suc
  isProp⟨has-suc⟩ = isOfHLevelRespectEquiv 1 Σ-Π-≃ (isOfHLevelΠ 1 λ _ → suc-unique _)

  isProp⟨is-suc⟩ : {a : A} → isProp (is-suc a)
  isProp⟨is-suc⟩ = isPropPropTrunc

  isProp⟨is-strong-suc-of⟩ : {a b : A} → isProp (a is-strong-suc-of b)
  isProp⟨is-strong-suc-of⟩ =
    isProp× isProp⟨is-suc-of⟩
            (isPropΠ2 λ _ _ → isProp⟨≤⟩ _ _ )

  isProp⟨is-strong-suc⟩ : {a : A} → isProp (is-strong-suc a)
  isProp⟨is-strong-suc⟩ {a} (b₁ , is-suc₁ , is-pred₁) (b₂ , is-suc₂ , is-pred₂) =
    Σ≡Prop (λ _ → isProp⟨is-strong-suc-of⟩)
           (≤-antisym _ _ (is-pred₂ b₁ (fst is-suc₁)) (is-pred₁ b₂ (fst is-suc₂)))

  -- A useful lemma:
  -- a function s calculates successors IFF b < a ↔ s b ≤ a
  calc-suc↔≤-<-characterization : (s : A → A) →
    (calc-suc s)
      ↔
    ((b a : A) → ((b < a) ↔ (s b ≤ a)))
  calc-suc↔≤-<-characterization s =
    (λ s-is-suc b a → snd (s-is-suc b) a ,
                      λ sb≤a → <∘≤-in-< (fst (s-is-suc b)) sb≤a)
    ,
    λ char b → snd (char b (s b)) (≤-refl (s b)) ,
    λ a → fst (char b a)

  isProp⟨is-sup-of⟩ : ∀ {ℓ a}{X : Type ℓ} {f} → isProp (a is- X -sup-of f)
  isProp⟨is-sup-of⟩ = isProp× (isPropΠ λ _ → isProp⟨≤⟩ _ _) (isPropΠ2 λ _ _ → isProp⟨≤⟩ _ _)

  isProp⟨calc-sup⟩ : (⊔ : (ℕ → A) → A) → isProp (calc-sup ⊔)
  isProp⟨calc-sup⟩ ⊔ = isPropΠ λ _ → isProp⟨is-sup-of⟩

  isProp⟨has-sup⟩ : isProp has-sup
  isProp⟨has-sup⟩ (⊔₁ , proof₁) (⊔₂ , proof₂) =
    Σ≡Prop (λ _ → isProp⟨calc-sup⟩ _)
           (funExt {f = ⊔₁} {g = ⊔₂} λ f →
             ≤-antisym _ _ (snd (proof₁ f) (⊔₂ f) (fst (proof₂ f)))
                       (snd (proof₂ f) (⊔₁ f) (fst (proof₁ f))))

  sup-zero : ∀ {a f} → is-zero a → a is-sup-of f → ∀ n → f n ≡ a
  sup-zero {a} {f} p q n = ≤-antisym _ _ (fst q n) (p (f n))

  sup-constant : ∀ {a c f} → a is-sup-of f → (∀ n → f n ≡ c) → a ≡ c
  sup-constant {a} {c} p q = ≤-antisym _ _ (snd p c (≤-reflexive ∘ q)) (subst (_≤ a) (q 0) (fst p 0))

  sup-unique : ∀ {a b f} → a is-sup-of f → b is-sup-of f → a ≡ b
  sup-unique {a} {b} {f} (f≤a , a-min-over-f) (f≤b , b-min-over-f) = ≤-antisym _ _ a≤b b≤a
   where
    a≤b : a ≤ b
    a≤b = a-min-over-f b f≤b
    b≤a : b ≤ a
    b≤a = b-min-over-f a f≤a

  isProp⟨is-lim⟩ : {a : A} → isProp (is-lim a)
  isProp⟨is-lim⟩ = isPropPropTrunc

  isProp⟨is-general-lim⟩ : (a : A) → isProp (is-general-lim a)
  isProp⟨is-general-lim⟩ a = isProp× isPropPropTrunc isProp⟨is-sup-of⟩

  is-general-lim-some-family→is-general-lim :
    ∀ {ℓ} → (a : A) → (X : Type ℓ) → (f : X → A) → ∥ X ∥ →
    (a is- X -sup-of f) → ((x : X) → f x < a) → is-general-lim a
  is-general-lim-some-family→is-general-lim a X f ∥x∥ a-sup a-strictly-greater
    = ∥-∥rec (isProp⟨is-general-lim⟩ a)
            (λ x → ∣ f x , a-strictly-greater x ∣ ,
                   (λ (x , x<a) → <-in-≤ x<a) ,
                   λ c h → snd a-sup c λ x → h (f x , a-strictly-greater x))
            ∥x∥

  is-ℕ-lim→is-general-lim : (a : A) → is-lim a → is-general-lim a
  is-ℕ-lim→is-general-lim a a-lim =
    ∥-∥rec (isProp⟨is-general-lim⟩ a)
          (λ ((f , f↑) , a-sup) → is-general-lim-some-family→is-general-lim a ℕ f ∣ 0 ∣ a-sup λ n → <∘≤-in-< (f↑ n) (fst a-sup (suc n)))
          a-lim

  -- `a : A` can only be one out of {zero, strong successor, limit}.
  -- We first show that `a` can't be two out of {zero, strong successor, limit} at the same time.
  module unique (a : A) where

    -- Easy: `a` can't be zero and strong successor simultaneously.
    not-z-and-s : (is-zero a) → (is-strong-suc a) → ⊥
    not-z-and-s is-z (b , (b<a , _) , _) = <-irrefl b (<∘≤-in-< b<a (is-z b))

    -- `a` can't be zero and limit.
    -- We need to eliminate out of the propositional truncation. In cubical Agda, we can choose
    -- whether we use the "old-style" truncation recursion principle, proved in the library, or
    -- the new pattern matching for HITs. Here, we use the old-style principle;
    -- for the suc-lim case below, we use the new pattern matching.
    not-z-and-gen-l : (is-zero a) → (is-general-lim a) → ⊥
    not-z-and-gen-l is-z (inhabited , fst≤a , _) = ∥-∥rec isProp⊥ (λ { (x , x<a) →
      <-irrefl x (<∘≤-in-< x<a (is-z x)) }) inhabited

    not-z-and-l : (is-zero a) → (is-lim a) → ⊥
    not-z-and-l is-z is-lim = not-z-and-gen-l is-z (is-ℕ-lim→is-general-lim a is-lim)

    -- The hardest case: `a` can't be strong successor and limit simultaneously.
    not-s-and-gen-l : (is-strong-suc a) → (is-general-lim a) → ⊥
    not-s-and-gen-l (b , (b<a , a-min-over-b) , b-max) (∣ x ∣ , fst≤a , a-least) = <-irrefl b b<b
      where
      a≤b : a ≤ b
      a≤b = a-least b λ { (x , x<a) → b-max x x<a }
      b<b : b < b
      b<b = <∘≤-in-< b<a a≤b
    not-s-and-gen-l a-str-suc (squash x y i , fst≤a , a-least) = isProp⊥ (not-s-and-gen-l a-str-suc (x , fst≤a , a-least))
                                                                         (not-s-and-gen-l a-str-suc (y , fst≤a , a-least)) i

    not-s-and-l : (is-strong-suc a) → (is-lim a) → ⊥
    not-s-and-l is-str-suc is-lim = not-s-and-gen-l is-str-suc (is-ℕ-lim→is-general-lim a is-lim)

  open unique

  -- Uniqueness of classification. We simply put everything from above together.
  -- ⊎ is not declared left or right associative, thus we need brackets in the statement.
  isProp⟨is-classifiable⟩ : (a : A) → isProp (is-classifiable a)
  isProp⟨is-classifiable⟩ a (inl z₁) (inl z₂) =
      cong inl (isProp⟨is-zero⟩ a _ _)
  isProp⟨is-classifiable⟩ a (inl z₁) (inr (inl s₂)) =
      ⊥.elim {A = λ _ → (inl z₁) ≡ inr (inl {B = is-lim a} s₂)} (not-z-and-s a z₁ s₂)
  isProp⟨is-classifiable⟩ a (inl z₁) (inr (inr l₂)) =
      ⊥.elim {A = λ _ → (inl z₁) ≡ inr (inr {A = is-strong-suc a} l₂)} (not-z-and-l a z₁ l₂)
  isProp⟨is-classifiable⟩ a (inr (inl s₁)) (inl z₂) =
      sym (isProp⟨is-classifiable⟩ a (inl z₂) (inr (inl s₁)))
  isProp⟨is-classifiable⟩ a (inr (inl s₁)) (inr (inl s₂)) =
      cong inr (cong inl (isProp⟨is-strong-suc⟩ s₁ s₂))
  isProp⟨is-classifiable⟩ a (inr (inl s₁)) (inr (inr l₂)) =
      ⊥.elim {A = λ _ → (inr {A = is-zero a} (inl s₁)) ≡ (inr (inr l₂))} (not-s-and-l a s₁ l₂)
  isProp⟨is-classifiable⟩ a (inr (inr l₁)) (inl z₂) =
      sym (isProp⟨is-classifiable⟩ a (inl z₂) (inr (inr l₁)))
  isProp⟨is-classifiable⟩ a (inr (inr l₁)) (inr (inl s₂)) =
      sym (isProp⟨is-classifiable⟩ a (inr (inl s₂)) (inr (inr l₁)))
  isProp⟨is-classifiable⟩ a (inr (inr l₁)) (inr (inr l₂)) =
      cong inr (cong inr (isProp⟨is-lim⟩ l₁ l₂))

  -- Similarly we have all the pieces to prove uniqueness of weak classification
  isProp⟨is-weakly-classifiable⟩ : (a : A) → isProp (is-weakly-classifiable a)
  isProp⟨is-weakly-classifiable⟩ a (inl z₁) (inl z₂) =
      cong inl (isProp⟨is-zero⟩ a _ _)
  isProp⟨is-weakly-classifiable⟩ a (inl z₁) (inr (inl s₂)) =
      ⊥.elim {A = λ _ → (inl z₁) ≡ inr (inl {B = is-general-lim a} s₂)} (not-z-and-s a z₁ s₂)
  isProp⟨is-weakly-classifiable⟩ a (inl z₁) (inr (inr l₂)) =
      ⊥.elim {A = λ _ → (inl z₁) ≡ inr (inr {A = is-strong-suc a} l₂)} (not-z-and-gen-l a z₁ l₂)
  isProp⟨is-weakly-classifiable⟩ a (inr (inl s₁)) (inl z₂) =
      sym (isProp⟨is-weakly-classifiable⟩ a (inl z₂) (inr (inl s₁)))
  isProp⟨is-weakly-classifiable⟩ a (inr (inl s₁)) (inr (inl s₂)) =
      cong inr (cong inl (isProp⟨is-strong-suc⟩ s₁ s₂))
  isProp⟨is-weakly-classifiable⟩ a (inr (inl s₁)) (inr (inr l₂)) =
      ⊥.elim {A = λ _ → (inr {A = is-zero a} (inl s₁)) ≡ (inr (inr l₂))} (not-s-and-gen-l a s₁ l₂)
  isProp⟨is-weakly-classifiable⟩ a (inr (inr l₁)) (inl z₂) =
      sym (isProp⟨is-weakly-classifiable⟩ a (inl z₂) (inr (inr l₁)))
  isProp⟨is-weakly-classifiable⟩ a (inr (inr l₁)) (inr (inl s₂)) =
      sym (isProp⟨is-weakly-classifiable⟩ a (inr (inl s₂)) (inr (inr l₁)))
  isProp⟨is-weakly-classifiable⟩ a (inr (inr l₁)) (inr (inr l₂)) =
      cong inr (cong inr (isProp⟨is-general-lim⟩ a l₁ l₂))

  isProp⟨has-classification⟩ : isProp has-classification
  isProp⟨has-classification⟩ = isPropΠ isProp⟨is-classifiable⟩

  classifiability-induction→has-classification :
    satisfies-classifiability-induction _ → has-classification
  classifiability-induction→has-classification ci =
    ci isProp⟨is-classifiable⟩
       (λ a is-zero → inl is-zero)
       (λ a b a-is-suc-of-b _ → inr (inl (b , a-is-suc-of-b)))
       (λ a f f↑ a-is-lim-of-f _ → inr (inr ∣ (f , f↑) , a-is-lim-of-f ∣))

  {- Classifiability induction -}

  module ClassifiabilityInduction
    (cc : has-classification)
    (wf : isWellFounded _<_)
    where

    ind : ∀ {ℓ} {P : A → Type ℓ}
        → (∀ a → isProp (P a))
        → (∀ a → is-zero a → P a)
        → (∀ a b → a is-strong-suc-of b → P b → P a)
        → (∀ a f f↑ → a is-lim-of (f , f↑) → (∀ i → P (f i)) → P a)
        → ∀ a → P a
    ind {_} {P} pvP pz ps pl = WFI.induction wf step
     where
      step : ∀ a → (∀ b → b < a → P b) → P a
      step a h with cc a
      ... | inl a-is-zero = pz a a-is-zero
      ... | inr (inl (b , a-is-suc-of-b)) = ps a b a-is-suc-of-b (h b (fst (fst a-is-suc-of-b)))
      ... | inr (inr a-is-lim) = ∥-∥rec (pvP a) claim a-is-lim
       where
        claim : is-Σlim a → P a
        claim ((f , f↑) , a-is-sup-of-f) = pl a f f↑ a-is-sup-of-f (λ i → h (f i) (f<a i))
         where
          f<a : ∀ i → f i < a
          f<a i = <∘≤-in-< (f↑ i) (fst a-is-sup-of-f (suc i))


--
-- Assume that A has zero, successor and limits of <-increasing sequences.
-- If A has decidable equality, then WLPO holds.
--
module no-go
  (<-irrefl : isIrrefl _<_)
  (<-trans : isTransitive _<_)
  (≤-antisym : isAntisym _≤_)
  (<∘≤-in-< : {a b c : A} → a < b → b ≤ c → a < c)
  (A-has-zero   : has-zero)
  (A-has-suc    : has-suc)
  (A-has-limits : has-limits)
 where
  <-irreflexive : {a b : A} → a ≡ b → ¬ (a < b)
  <-irreflexive {a} {b} p = subst (λ x → ¬ (a < x)) p (<-irrefl a)

  z : A
  z = fst A-has-zero
  s : A → A
  s = fst A-has-suc
  lim : IncrSeq → A
  lim = fst A-has-limits

  -- Embedding of natural numbers into A
  ι : ℕ → A
  ι  0      = z
  ι (suc i) = s (ι i)
  ι-inc : is-<-increasing ι
  ι-inc i = fst (snd A-has-suc (ι i))

  -- ω is the limit of ι
  ω : A
  ω = lim (ι , ι-inc)
  ι<ω : ∀ i → ι i < ω
  ι<ω i = <∘≤-in-< claim₀ claim₁
   where
    claim₀ : ι i < ι (suc i)
    claim₀ = ι-inc i
    claim₁ : ι (suc i) ≤ ω
    claim₁ = fst (snd A-has-limits (ι , ι-inc)) (suc i)

  -- Jumping sequence: (t ↑) "jumps" as soon as a tt is discovered in t.
  _↑ : (ℕ → Bool) → ℕ → A
  (t ↑)  0      = z
  (t ↑) (suc i) = if (least-index-true t i) then ω else (s ((t ↑) i))

  ↑-spec-≡ι : (t : ℕ → Bool)
    → (n : ℕ) → (∀ i → i N.< n → t i ≡ ff)
    → (t ↑) n ≡ ι n
  ↑-spec-≡ι t 0 p = refl
  ↑-spec-≡ι t (suc n) p = goal
   where
    claim₀ : ∀ i → i N.≤ n → t i ≡ ff
    claim₀ i i≤n = p i (N.suc-≤-suc i≤n)
    claim₁ : least-index-true t n ≡ ff
    claim₁ = least-index-true-spec-ff t n claim₀
    claim₂ : (t ↑) (suc n) ≡ s((t ↑) n)
    claim₂ = cong (if_then ω else s((t ↑) n)) claim₁
    IH : (t ↑) n ≡ ι n
    IH = ↑-spec-≡ι t n (λ i i<n → p i (N.≤-suc i<n))
    claim₃ : s((t ↑) n) ≡ ι (suc n)
    claim₃ = cong s IH
    goal : (t ↑) (suc n) ≡ ι (suc n)
    goal = claim₂ ∙ claim₃

  ↑-spec-<ω : (t : ℕ → Bool)
    → (i : ℕ) → least-index-true t i ≡ tt
    → (t ↑) i < ω
  ↑-spec-<ω t i p = subst (_< ω) (sym claim₀) claim₁
   where
    q : ∀ j → j N.< i → t j ≡ ff
    q = least-index-true-case-tt t i p
    claim₀ : (t ↑) i ≡ ι i
    claim₀ = ↑-spec-≡ι t i q
    claim₁ : ι i < ω
    claim₁ = ι<ω i

  ↑-inc : (t : ℕ → Bool) → is-<-increasing (t ↑)
  ↑-inc t i with least-index-true t i ≟ tt
  ↑-inc t i | yes p = goal
   where
    claim₀ : (t ↑) (suc i) ≡ ω
    claim₀ = cong (if_then ω else s((t ↑) i)) p
    claim₁ : (t ↑) i < ω
    claim₁ = ↑-spec-<ω t i p
    goal : (t ↑) i < (t ↑) (suc i)
    goal = subst ((t ↑) i <_) (sym claim₀) claim₁
  ↑-inc t i | no ¬p = goal
   where
    p : least-index-true t i ≡ ff
    p = ¬true→false _ ¬p
    claim₀ : (t ↑) (suc i) ≡ s ((t ↑) i)
    claim₀ = cong (if_then ω else s((t ↑) i)) p
    claim₁ : (t ↑) i < s ((t ↑) i)
    claim₁ = fst (snd A-has-suc ((t ↑) i))
    goal : (t ↑) i < (t ↑) (suc i)
    goal = subst ((t ↑) i <_) (sym claim₀) claim₁

  ↑-inc' : (t : ℕ → Bool) (i j : ℕ) → i N.< j → (t ↑) i < (t ↑) j
  ↑-inc' t i 0 i<0 = ⊥.rec (N.¬-<-zero i<0)
  ↑-inc' t i (suc j) (0 , i+1≡j+1) = subst (λ x → (t ↑) i < (t ↑) x) i+1≡j+1 (↑-inc t i)
  ↑-inc' t i (suc j) (suc k , k+i+1≡j) = <-trans _ _ _ IH fact
   where
    IH : (t ↑) i < (t ↑) j
    IH = ↑-inc' t i j (k , injSuc k+i+1≡j)
    fact : (t ↑) j < (t ↑) (suc j)
    fact = ↑-inc t j

  ↑-spec->ω : (t : ℕ → Bool)
    → (i : ℕ) → t i ≡ tt
    → ω < (t ↑) (suc (suc i))
  ↑-spec->ω t i ti≡tt = goal
   where
    n : ℕ
    n = fst (least-index-true-spec-tt t i ti≡tt)
    n≤i : n N.≤ i
    n≤i = fst (snd (least-index-true-spec-tt t i ti≡tt))
    p : least-index-true t n ≡ tt
    p = snd (snd (least-index-true-spec-tt t i ti≡tt))
    claim₀ : (t ↑) (suc n) ≡ ω
    claim₀ = cong (if_then ω else s((t ↑) n)) p
    n+1<i+2 : suc n N.< suc (suc i)
    n+1<i+2 = N.suc-≤-suc (N.suc-≤-suc n≤i)
    claim₁ : (t ↑) (suc n) < (t ↑) (suc (suc i))
    claim₁ = ↑-inc' t (suc n) (suc (suc i)) n+1<i+2
    goal : ω < (t ↑) (suc (suc i))
    goal = subst (_< (t ↑) (suc (suc i))) claim₀ claim₁

  case-ω<lim↑ : (t : ℕ → Bool)
    → ∀ i → t i ≡ tt → ω < lim (t ↑ , ↑-inc t)
  case-ω<lim↑ t i p = <∘≤-in-< claim₀ claim₁
   where
    claim₀ : ω < (t ↑) (suc (suc i))
    claim₀ = ↑-spec->ω t i p
    claim₁ : (t ↑) (suc (suc i)) ≤ lim (t ↑ , ↑-inc t)
    claim₁ = fst (snd A-has-limits (t ↑ , ↑-inc t)) (suc (suc i))

  case-lim↑≡ω : (t : ℕ → Bool)
    → (∀ i → t i ≡ ff) → lim (t ↑ , ↑-inc t) ≡ ω
  case-lim↑≡ω t p = ≤-antisym _ _ lim≤ω ω≤lim
   where
    claim₀ : ∀ i → (t ↑) i ≡ ι i
    claim₀ i = ↑-spec-≡ι t i (λ i _ → p i)
    claim₁ : ∀ i → (t ↑) i ≤ ω
    claim₁ i = subst (_≤ ω) (sym (claim₀ i)) (fst (snd A-has-limits (ι , ι-inc)) i)
    claim₂ : ∀ i → ι i ≤ lim (t ↑ , ↑-inc t)
    claim₂ i = subst (_≤ lim (t ↑ , ↑-inc t)) (claim₀ i) (fst (snd A-has-limits (t ↑ , ↑-inc t)) i)
    lim≤ω : lim (t ↑ , ↑-inc t) ≤ ω
    lim≤ω = snd (snd A-has-limits (t ↑ , ↑-inc t)) ω claim₁
    ω≤lim : ω ≤ lim (t ↑ , ↑-inc t)
    ω≤lim = snd (snd A-has-limits (ι , ι-inc)) (lim (t ↑ , ↑-inc t)) claim₂

  no-go-theorem : Discrete A → WLPO
  no-go-theorem d t = goal
   where
    t↑ : ℕ → A
    t↑ = t ↑
    a : A
    a = lim (t↑ , ↑-inc t)
    goal : (∀ i → t i ≡ ff) ⊎ (¬(∀ i → t i ≡ ff))
    goal with d a ω
    ... | yes a≡ω = inl subgoal
     where
      subgoal : ∀ i → t i ≡ ff
      subgoal i = ¬true→false (t i) (λ p → <-irreflexive (sym a≡ω) (case-ω<lim↑ t i p))
    ... | no ¬a≡ω = inr subgoal
     where
      subgoal : ¬ (∀ i → t i ≡ ff)
      subgoal q = ¬a≡ω (case-lim↑≡ω t q)
