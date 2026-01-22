----------------------------------------------------------------------------------------------------
-- Some properties of Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness --safe #-}

module BrouwerTree.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat as N hiding (isZero)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import PropTrunc

open import BrouwerTree.Base

open import BrouwerTree.Properties.Core public

Brw-is-set : isSet Brw
Brw-is-set = trunc

isProp⟨<⟩ : ∀ {x y} → isProp (x < y)
isProp⟨<⟩ = ≤-trunc

isProp⟨≤⟩ : ∀ {x y} → isProp (x ≤ y)
isProp⟨≤⟩ = ≤-trunc

{- ≤ is reflexive -}

≤-refl-≡ : ∀ {x y} → x ≡ y → x ≤ y
≤-refl-≡ {x} {y} x≡y = subst (λ z → z ≤ y) (sym x≡y) ≤-refl

{- Limits of pointwise equal sequences are equal -}

limit-pointwise-equal : ∀ f {f↑} g {g↑} → ((n : ℕ) → f n ≡ g n) → limit f {f↑} ≡ limit g {g↑}
limit-pointwise-equal f g f≡g = bisim f g ((λ k → ∣ k , ≤-refl-≡ (f≡g k) ∣) ,
                                           (λ k → ∣ k , ≤-refl-≡ (sym (f≡g k)) ∣))

{- Some simple properties -}

simulation→≤ : ∀ {f f↑ g g↑} → (∀ k -> Σ[ n ∈ ℕ ] f k ≤ g n) -> limit f {f↑}  ≤ limit g {g↑}
simulation→≤ {f} {f↑} {g} {g↑} f≤g = ≤-limiting f λ k → ≤-cocone g (snd (f≤g k))

{- -- this is not a useful property
mere-simulation→≤ : ∀ {f f↑ g g↑} → ∥ (∀ k -> Σ[ n ∈ ℕ ] f k ≤ g n) ∥ -> limit f {f↑}  ≤ limit g {g↑}
mere-simulation→≤ {f} {f↑} {g} {g↑} = ∥-∥rec {P = limit f {f↑}  ≤ limit g {g↑}} ≤-trunc simulation→≤

Cf Code.Results.weakly-bisimilar→lim≤lim for a more useful property.
-}

pointwise≤→≤ : ∀ {f f↑ g g↑} → (∀ k -> f k ≤ g k) -> limit f {f↑}  ≤ limit g {g↑}
pointwise≤→≤ fk≤gk = simulation→≤ (λ k → (k , fk≤gk k))

least-upper-bound : ∀ {f g} {f↑ : increasing f}{g↑ : increasing g} → (∀ c → (∀ n → f n ≤ c) → limit g {g↑} ≤ c) → limit g {g↑} ≤ limit f {f↑}
least-upper-bound {f} {g} {f↑} {g↑} hyp = hyp (limit f) λ n → ≤-cocone-simple f


<-trunc : ∀ {x y} -> isProp (x < y)
<-trunc = ≤-trunc

<-in-≤ : ∀ {x y} → x < y → x ≤ y
<-in-≤ {x} x<y = ≤-trans (≤-succ-incr-simple {x}) x<y

<∘≤-in-< : ∀ {x y z} → x < y → y ≤ z → x < z
<∘≤-in-< x<y y≤z = ≤-trans x<y y≤z

≤∘<-in-< : ∀ {x y z} → x ≤ y → y < z → x < z
≤∘<-in-< {x} {y} {z} x≤y y<z = succ x ≤⟨ ≤-succ-mono x≤y ⟩ succ y ≤⟨ y<z ⟩ z ≤∎

<-trans : BinaryRelation.isTrans _<_
<-trans x y z x<y y<z = ≤-trans x<y (<-in-≤ y<z)

{- Predecessor -}

module predecessor where

  pred : Brw → Brw
  pred zero = zero
  pred (succ x) = x
  pred (limit f {f↑}) = limit f {f↑}
  pred (bisim f {f↑} g {g↑} f∼g i) = bisim f {f↑} g {g↑} f∼g i
  pred (trunc x y p q i j) = trunc (pred x) (pred y) (cong pred p) (cong pred q) i j

  pred-decr-simple : ∀ x → pred x ≤ x
  pred-decr-simple =
    Brw-ind (λ x → pred x ≤ x)
            (λ _ → ≤-trunc)
            ≤-zero
            (λ _ → ≤-succ-incr-simple)
            λ _ → ≤-refl

  succ-is-inj : ∀ {x y} → succ x ≡ succ y → x ≡ y
  succ-is-inj = cong pred

  pred-≤ : {x y : Brw} → y ≤ x → pred y ≤ pred x
  pred-≤ =
    ≤-ind (λ {y} {x} y≤x → pred y ≤ pred x)
          (λ _ → ≤-trunc)
          ≤-zero
          ≤-trans
          (λ y≤x _ → y≤x)
          (λ {y} f {f↑} {k} y≤fk py≤pfk →
             ≤-cocone {pred y} f {f↑} {k} (≤-trans (pred-decr-simple y) y≤fk))
          (λ f {f↑} {x} f≤x pf≤px f≤psx → ≤-limiting f {f↑} {pred x} λ k →
             f k              ≤⟨ f≤psx k ⟩
             pred (f (suc k)) ≤⟨ pf≤px (suc k) ⟩
             pred x           ≤∎)

  ≤-succ-mono⁻¹-alt : ∀ {x y} → succ x ≤ succ y → x ≤ y
  ≤-succ-mono⁻¹-alt = pred-≤

{- Distinguishing the constructors -}

isZero' : Brw → hProp ℓ-zero
isZero' zero = Unit , isPropUnit
isZero' (succ x) = ⊥ , isProp⊥
isZero' (limit f) = ⊥ , isProp⊥
isZero' (bisim f g x i) = ⊥ , isProp⊥
isZero' (trunc x y p q i j) =
  isSet→SquareP {A = λ i j → hProp ℓ-zero}
                (λ i j → isSetHProp)
                (λ j → isZero' (p j))
                (λ j → isZero' (q j))
                refl
                refl
                i j

isZero : Brw → Type
isZero x = typ (isZero' x)

isProp⟨isZero⟩ : {x : Brw} → isProp (isZero x)
isProp⟨isZero⟩ {x} = str (isZero' x)

zero≠succ : ∀ {x} → zero ≡ succ x → ⊥
zero≠succ {x} z≡sx = subst isZero z≡sx tt

zero≠lim : ∀ {f f↑} → zero ≡ limit f {f↑} → ⊥
zero≠lim {f} {f↑} zero≡⊔f = subst isZero zero≡⊔f tt

isZero-correct : ∀ {x} → isZero x → x ≡ zero
isZero-correct {x} iZ⟨x⟩ =
  Brw-ind (λ x → isZero x → x ≡ zero)
          (λ x → isPropΠ (λ _ → trunc x zero))
          (λ _ → refl)
          (λ _ ())
          (λ _ ())
          x iZ⟨x⟩

isDec⟨isZero⟩ : (x : Brw) → Dec (isZero x)
isDec⟨isZero⟩ = Brw-ind (λ x → Dec (isZero x)) (λ x → isPropDec (isProp⟨isZero⟩ {x}))
                  (yes tt)
                  (λ _ → no λ ())
                  (λ _ → no λ ())

decZero : (x : Brw) → Dec (x ≡ zero)
decZero x = mapDec isZero-correct (λ ¬isZ x≡zero → subst (λ z → isZero z → ⊥) x≡zero ¬isZ tt)
                   (isDec⟨isZero⟩ x)


isSucc' : Brw → hProp ℓ-zero
isSucc' zero = ⊥ , isProp⊥
isSucc' (succ x) = Unit , isPropUnit
isSucc' (limit f) = ⊥ , isProp⊥
isSucc' (bisim f g x i) = ⊥ , isProp⊥
isSucc' (trunc x y p q i j) =
  isSet→SquareP {A = λ i j → hProp ℓ-zero}
                (λ i j → isSetHProp)
                (λ j → isSucc' (p j))
                (λ j → isSucc' (q j))
                refl
                refl
                i j

isSucc : Brw → Type ℓ-zero
isSucc x = typ (isSucc' x)

succ≠lim : ∀ {x f f↑} → succ x ≡ limit f {f↑} → ⊥
succ≠lim sx≡⊔f = subst isSucc sx≡⊔f tt

{- Successors and limits are not smaller or equal to zero. -}

≤-isZero-function : ∀ {x y} → x ≤ y → isZero y → isZero x
≤-isZero-function {x} {y} = ≤-ind (λ {x} {y} x≤y → isZero y → isZero x)
                                  (λ {x} x≤y → isProp→ (isProp⟨isZero⟩ {x}))
                                  (λ _ → tt)
                                  (λ ih₁ ih₂ → ih₁ ∘ ih₂)
                                  (λ _ _ ())
                                  (λ {x} f {f↑} x≤fk ih ())
                                  λ f {f↑} {y} f≤y ih ih↑ iZ⟨y⟩ → ih↑ 0 (ih 1 iZ⟨y⟩)

succ≰zero-aux : ∀ {x y z} → y ≤ z → y ≡ succ x → isZero z → ⊥
succ≰zero-aux {x} {.zero} {z} ≤-zero y≡sx iZ⟨z⟩ = zero≠succ y≡sx
succ≰zero-aux {x} {y} {z} (≤-trans {y} {y₁} {z} y≤y₁ y₁≤z) y≡sx iZ⟨z⟩ =
    succ≰zero-aux y≤y₁ y≡sx (≤-isZero-function y₁≤z iZ⟨z⟩)
succ≰zero-aux {x} {.(limit f)} {z} (≤-limiting f x₁) y≡sx iZ⟨z⟩ = succ≠lim (sym y≡sx)
succ≰zero-aux {x} {y} {z} (≤-trunc y≤z y≤z₁ i) y≡sx iZ⟨z⟩ =
    isProp⊥ (succ≰zero-aux y≤z y≡sx iZ⟨z⟩) (succ≰zero-aux y≤z₁ y≡sx iZ⟨z⟩) i

succ≰zero : ∀ {x} → succ x ≤ zero → ⊥
succ≰zero {x} sx≤z = succ≰zero-aux sx≤z refl tt

x≮zero : ∀ {x} → x < zero → ⊥
x≮zero = succ≰zero

x≤zero→x≡zero : ∀ {x} → x ≤ zero → x ≡ zero
x≤zero→x≡zero x≤zero = isZero-correct (≤-isZero-function x≤zero tt)

lim≰zero : ∀ {f f↑} → limit f {f↑} ≤ zero → ⊥
lim≰zero {f} {f↑} ⊔f≤zero = succ≰zero (succ (f 0) ≤⟨ f↑ 0 ⟩
                                       f 1        ≤⟨ ≤-cocone-simple f {f↑} ⟩
                                       limit f    ≤⟨ ⊔f≤zero ⟩
                                       zero       ≤∎)

lim≢zero : ∀ {f f↑} → limit f {f↑} ≡ zero → ⊥
lim≢zero e = lim≰zero (subst (_≤ zero) (sym e) ≤-refl)

zero<succ : ∀ {x} → zero < succ x
zero<succ = ≤-succ-mono ≤-zero

zero<lim : ∀ {f f↑} → zero < limit f {f↑}
zero<lim {f} {f↑} = ≤-trans (≤-succ-mono (≤-zero {f 0})) (≤-trans (f↑ 0) (≤-cocone-simple f))

{- Embedding natural numbers into Brouwer trees -}

ι-mono : {n m : ℕ} → n N.≤ m → ι n ≤ ι m
ι-mono (zero , p) = ≤-refl-≡ (cong ι p)
ι-mono {n} {zero} (suc k , p) = ⊥.rec (snotz p)
ι-mono {n} {suc m} (suc k , p) = ≤-succ-incr (ι-mono {n} {m} (k , injSuc p))

ι-mono-< : {n m : ℕ} → n N.< m → ι n < ι m
ι-mono-< = ι-mono

ι-injective : {n m : ℕ} → ι n ≡ ι m → n ≡ m
ι-injective {zero} {zero} p = refl
ι-injective {zero} {suc m} p = ⊥.rec (zero≠succ p)
ι-injective {suc n} {zero} p = ⊥.rec ((zero≠succ (sym p)))
ι-injective {suc n} {suc m} p = cong suc (ι-injective {n} {m} (predecessor.succ-is-inj p))

ι-pointwise-smaller :  ∀ f (f↑ : increasing f) → (k : ℕ) → ι k ≤ f k
ι-pointwise-smaller f f↑ zero = ≤-zero
ι-pointwise-smaller f f↑ (suc k) = ≤-trans (≤-succ-mono (ι-pointwise-smaller f f↑ k)) (f↑ k)

ι_<lim : ∀ {f f↑} → (k : ℕ) → ι k < limit f {f↑}
ι_<lim {f} {f↑} k = ≤∘<-in-< (ι-pointwise-smaller f f↑ k) (<∘≤-in-< (f↑ k) (≤-cocone-simple f))

ι≰zero : (n : ℕ) → n N.> 0 → ι n ≤ zero → ⊥
ι≰zero zero l = ⊥.rec (N.¬m<m l)
ι≰zero (suc n) l = succ≰zero

zero≠x→zero<x : ∀ x → ¬ (zero ≡ x) → zero < x
zero≠x→zero<x = Brw-ind (λ x → ¬ (zero ≡ x) → zero < x) (λ x → isProp→ ≤-trunc)
                  (λ z≢z → ⊥.rec (z≢z refl))
                  (λ _ _ → zero<succ)
                  (λ _ _ → zero<lim)

one<x→x≢zero : ∀ {x} → one < x → ¬ x ≡ zero
one<x→x≢zero {x} one<x x≡zero = x≮zero (subst (λ z → one < z) x≡zero one<x)

one<lim : ∀ {f f↑} → one < limit f {f↑}
one<lim {f} {f↑} = ι 1 <lim

limit-skip-first : ∀ f {f↑} → limit f {f↑} ≡ limit (f ∘ suc) {f↑ ∘ suc}
limit-skip-first f {f↑} = bisim f (f ∘ suc)
                                ((λ k → ∣ k , <-in-≤ (f↑ k) ∣) , λ k → ∣ suc k , ≤-refl ∣)

limit-skip-finite
 : ∀ f {f↑} → (i : ℕ)
 → limit f {f↑} ≡ limit (λ n → f (n N.+ i)) {λ n → f↑ (n N.+ i)}
limit-skip-finite f 0 = limit-pointwise-equal _ _ λ n → cong f (sym (+-zero n))
limit-skip-finite f (suc i) =
 limit f
  ≡⟨ limit-skip-finite f i ⟩
 limit (λ n → f (n + i))
  ≡⟨ limit-skip-first (λ n → f (n N.+ i)) ⟩
 limit ((λ n → f (n + i)) ∘ suc)
  ≡⟨ limit-pointwise-equal _ _ (λ n → cong f (sym (+-suc n i))) ⟩
 limit (λ n → f (n + suc i))
  ∎

increasing-monotone : {f : ℕ → Brw} → increasing f → {n m : ℕ} → n N.≤ m → f n ≤ f m
increasing-monotone {f} f↑ {n} {m} (k , p) = go {f} f↑ {n} {m} k p where
  go : ∀ {f} (f↑ : increasing f) {n} {m} n₁ (p : n₁ + n ≡ m) → f n ≤ f m
  go {f} f↑ {n} {m} zero p = ≤-refl-≡ (cong f p)
  go {f} f↑ {n} {m} (suc k) p = <-in-≤ (<∘≤-in-< (f↑ n) (go f↑ k (+-suc k n ∙ p)))

{- Deciding if = 0, =1 or > 1 -}

decZeroOneMany : (x : Brw) → (x ≡ zero) ⊎ ((x ≡ one) ⊎ (one < x))
decZeroOneMany zero = inl refl
decZeroOneMany (succ x) with decZeroOneMany x
... | inl x≡zero = inr (inl (cong succ x≡zero))
... | inr (inl x≡one) = inr (inr (≤-succ-mono (≤-refl-≡ (sym x≡one))))
... | inr (inr one<x) = inr (inr (≤-succ-incr one<x))
decZeroOneMany (limit f) = inr (inr one<lim)
decZeroOneMany (bisim f {f↑} g {g↑} p i) = inr (inr (isProp→PathP {B = λ i → one < bisim f g p i}
                                                                  (λ i → <-trunc)
                                                                  one<lim one<lim i))
decZeroOneMany (trunc x y p q i j) =
    isSet→SquareP {A = λ i j → (trunc x y p q i j ≡ zero)
                             ⊎ ((trunc x y p q i j ≡ one)
                             ⊎ (one < trunc x y p q i j))}
                  (λ i j → isSet⊎ (isProp→isSet (Brw-is-set _ _))
                                    (isSet⊎ (isProp→isSet (Brw-is-set _ _))
                                              (isProp→isSet <-trunc)))
                  (λ j → decZeroOneMany (p j)) (λ j → decZeroOneMany (q j)) refl refl i j
