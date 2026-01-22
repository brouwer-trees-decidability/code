----------------------------------------------------------------------------------------------------
-- Arithmetic operations on Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Arithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
  using (ℕ; zero; suc)
  renaming (_+_ to _N+_)
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Nullary

open import PropTrunc

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Code
open import BrouwerTree.Code.Results

infixr 36 _·_
infixr 37 _^_

{- Addition -}

open import BrouwerTree.Arithmetic.Addition public

zero+y≡y : ∀ y → zero + y ≡ y
zero+y≡y =
  Brw-ind (λ y → zero + y ≡ y)
          (λ x → Brw-is-set _ _)
          refl
          (cong succ)
          (λ {f} {f↑} ih → bisim (λ n → zero + f n) f
                                 ((λ k → ∣ k , subst (λ z → z ≤ f k) (sym (ih k)) ≤-refl ∣) ,
                                  (λ k → ∣ k , subst (λ z → f k ≤ z) (sym (ih k)) ≤-refl ∣)))

+x-increasing : ∀ {y} → (x : Brw) → x ≤ y + x
+x-increasing {y} =
  Brw-ind (λ x → x ≤ y + x)
          (λ x → ≤-trunc)
          ≤-zero
          ≤-succ-mono
          (λ {f} {f↑} ih → ≤-limiting f (λ k → ≤-trans (ih k) (≤-cocone-simple (λ n → y + f n))))

+-mono : ∀ {x y x' y'} → x ≤ x' → y ≤ y' → x + y ≤ x' + y'
+-mono {x} {y} {x'} {y'} p q = ≤-trans (+x-mono y p) (x+-mono q)

x+-mono-< : {x y z : Brw} → y < z → x + y < x + z
x+-mono-< {x} {y} {z} y<z = x+-mono y<z

+-leftCancel-≤ : ∀ x y z → x + y ≤ x + z → y ≤ z
+-leftCancel-≤ x y z p = Brw-ind (λ a → ∀ z → x + a ≤ x + z → a ≤ z) (λ a → isPropΠ λ x → isProp→ ≤-trunc)
                                 (λ z _ → ≤-zero)
                                 (λ {y} ihy → Brw-ind (λ b → succ (x + y) ≤ (x + b) → succ y ≤ b) (λ x → isProp→ ≤-trunc)
                                                      (λ p → ⊥.rec (<-irreflexive _ (<∘≤-in-< (≤∘<-in-< (x+-mono {z = y} ≤-zero) ≤-refl) p)))
                                                      (λ {z} ihz p → ≤-succ-mono (ihy z (≤-succ-mono⁻¹ p)))
                                                      λ {f} ihz p → ∥-∥rec ≤-trunc (λ (n , q) → ≤-cocone f (ihz n q)) (below-limit-lemma (x + y) _ p))
                                 (λ {f} {f↑} ihf → Brw-ind (λ b →  limit (λ n → x + f n) ≤ (x + b) → limit f ≤ b) (λ x → isProp→ ≤-trunc)
                                                           (λ p → ⊥.rec (<-irreflexive x (<∘≤-in-< (≤∘<-in-< (x+-mono {z = f 17} ≤-zero) (<-cocone-simple (λ n → x + f n) {k = 17})) p)))
                                                           (λ {z} ihz p → ≤-limiting f λ k → ihf k (succ z) (≤-trans (≤-cocone-simple _) p))
                                                           λ {g} {g↑} ihg p → weakly-bisimilar→lim≤lim f g (λ k → ∥-∥rec squash (λ (n , q) → ∣ n , ihf k (g n) q ∣) (lim≤lim→weakly-bisimilar _ _ p k)))
                                 y z p

+-leftCancel : ∀ x {y z} → x + y ≡ x + z → y ≡ z
+-leftCancel x {y} {z} x+y≡x+z = ≤-antisym (+-leftCancel-≤ x y z (≤-refl-≡ x+y≡x+z ))
                                           (+-leftCancel-≤ x z y (≤-refl-≡ (sym x+y≡x+z)))

+-leftCancel-< : ∀ x {y z} → x + y < x + z → y < z
+-leftCancel-< x {y} {z} p = +-leftCancel-≤ x (succ y) z p



{- # Multiplication -}

mutual

  _·_ : Brw → Brw → Brw
  x · zero = zero
  x · (succ y) = x · y + x
  x · (limit f {f↑}) with decZero x
  ... | yes x≡zero = zero
  ... | no x≢zero = limit (λ n → x · (f n)) {x·-increasing x≢zero f↑}
  x · (bisim f {f↑} g {g↑} (f≲g , g≲f) i) with decZero x
  ... | yes x≡zero = refl {x = zero} i
  ... | no x≢zero = bisim (λ n → x · f n) {x·-increasing x≢zero f↑}
                          (λ n → x · g n) {x·-increasing x≢zero g↑}
                          (x·-preserves-≲ f≲g , x·-preserves-≲ g≲f) i
  x · (trunc y z p q i j) =  trunc (x · y) (x · z) (λ j → x · (p j)) (λ j → x · (q j)) i j

  x·-mono : ∀ {x y z : Brw} → y ≤ z → x · y ≤ x · z
  x·-mono ≤-zero = ≤-zero
  x·-mono (≤-trans y≤w w≤z) = ≤-trans (x·-mono y≤w) (x·-mono w≤z)
  x·-mono {x} (≤-succ-mono {y} {z} y≤z) = +x-mono x (x·-mono {x} y≤z)
  x·-mono {x} {y} (≤-cocone f {k = k} y≤z) with decZero x
  ... | yes x≡zero = subst (λ z → z ≤ zero) (sym (zero·y≡zero y) ∙ cong (_· y) (sym x≡zero)) ≤-refl
  ... | no x≢zero = ≤-cocone (λ n → x · f n) {k = k} (x·-mono y≤z)
  x·-mono {x} (≤-limiting f f≤z) with decZero x
  ... | yes x≡zero = ≤-zero
  ... | no x≢zero = ≤-limiting (λ n → x · f n) λ k → x·-mono (f≤z k)
  x·-mono (≤-trunc p q i) = ≤-trunc (x·-mono p) (x·-mono q) i

  zero·y≡zero : ∀ y → zero · y ≡ zero
  zero·y≡zero zero = refl
  zero·y≡zero (succ y) = zero·y≡zero y
  zero·y≡zero (limit f) = refl
  zero·y≡zero (bisim f g x i) = refl
  zero·y≡zero (trunc x y p q i j) =
    isProp→SquareP {B = λ i j → trunc (zero · x) (zero · y)
                                      (λ j₁ → zero · p j₁) (λ j₁ → zero · q j₁) i j
                              ≡ zero}
                   (λ i j → Brw-is-set _ _)
                   (λ j → zero·y≡zero x)
                   (λ j → zero·y≡zero y)
                   (λ j → zero·y≡zero (p j))
                   (λ j → zero·y≡zero (q j)) i j

  x·-mono-< : {x y z : Brw} → (x ≡ zero → ⊥) → y < z → x · y < x · z
  x·-mono-< {x} x≢zero y<z = <∘≤-in-< (x+-mono-< (zero≠x→zero<x _ λ zero≡x → x≢zero (sym zero≡x)))
                                      (x·-mono {x} y<z)

  x·-increasing : ∀ {x f} → ¬ (x ≡ zero) → increasing f → increasing (λ n → x · f n)
  x·-increasing {x} {f} x≢zero f↑ k = x·-mono-< x≢zero (f↑ k)

  -- See the discussion in Line 58.
  {-# TERMINATING #-}
  x·-preserves-≲ : ∀ {x f g} → f ≲ g → (λ n → x · f n) ≲ (λ n → x · g n)
  x·-preserves-≲ f≲g k = ∥-∥rec isPropPropTrunc (λ { (l , fk≤gl) → ∣ l , x·-mono fk≤gl ∣ }) (f≲g k)

·x-mono : ∀ {x y} → (z : Brw) → x ≤ y → x · z ≤ y · z
·x-mono {x} {y} z x≤y = Brw-ind (λ z → x · z ≤ y · z)
                                (λ z → ≤-trunc)
                                ≤-refl
                                (λ {z} ih → +-mono ih x≤y)
                                (limit-case x≤y)
                                z
 where
  limit-case : ∀ {x} {y} {f} {f↑} → x ≤ y → (∀ k → (x · f k) ≤ (y · f k)) →
                 (x · limit f {f↑}) ≤ (y · limit f {f↑})
  limit-case {x} {y} {f} {f↑} x≤y ih with decZero x | decZero y
  ... | yes x≡zero | _ = ≤-zero
  ... | no x≢zero | yes y≡zero =
    ⊥.rec (<-irreflexive _ (subst (λ z → zero < z) y≡zero
                                  (<∘≤-in-< (zero≠x→zero<x _ λ zero≡x → x≢zero (sym zero≡x)) x≤y)))
  ... | no x≢zero | no y≠zero = weakly-bisimilar→lim≤lim (λ n → x · f n)
                                                         (λ n → y · f n)
                                                         (λ k → ∣ k , ih k ∣)

·-mono : {x x' y y' : Brw} → x ≤ x' → ¬ (x' ≡ zero) → y < y' → x · y < x' · y'
·-mono {x} {x'} {y} {y'} x≤x' x'≠0 y<y' = ≤∘<-in-< (·x-mono y x≤x') (x·-mono-< x'≠0 y<y')

+-not-zero-not-zero : ∀ {a b} → ¬ (a ≡ zero) → ¬ (b + a ≡ zero)
+-not-zero-not-zero {a} {b} =
  Brw-ind (λ a → ¬ (a ≡ zero) → ¬ (b + a ≡ zero))
          (λ a → isProp→ (isProp¬ _))
          (λ a≢zero → ⊥.rec (a≢zero refl))
          (λ _ _ → λ zero≡succ → zero≠succ (sym zero≡succ))
          (λ _ _ → λ lim≡succ → zero≠lim (sym lim≡succ))
          a

·-no-zero-divisors : ∀ {a b} → ¬ (a ≡ zero) → ¬ (b ≡ zero) → ¬ (a · b) ≡ zero
·-no-zero-divisors {a} {b} =
  Brw-ind (λ b → ¬ (a ≡ zero) → ¬ (b ≡ zero) → ¬ (a · b) ≡ zero)
          (λ x → isProp→ (isProp→ (isProp¬ _)))
          (λ _ nonsense → nonsense)
          (λ _ a≢zero _ → +-not-zero-not-zero a≢zero)
          (λ {f} {f↑} ih a≢zero _ → limitcase a f f↑ ih a≢zero)
          b
  where
    limitcase : ∀ a f f↑ → (∀ k → ¬ a ≡ zero → ¬ f k ≡ zero → ¬ a · f k ≡ zero) →
                  ¬ a ≡ zero → ¬ a · limit f {f↑} ≡ zero
    limitcase a f f↑ ih a≢zero with decZero a
    ... | yes a≡zero = ⊥.rec (a≢zero a≡zero)
    ... | no _ = λ p → (zero≠lim (sym p))

not-zero-·-limit : ∀ x f f↑ → (x≢zero : ¬ (x ≡ zero))
  → x · limit f {f↑} ≡ limit (λ n → x · (f n)) {x·-increasing x≢zero f↑}
not-zero-·-limit x f f↑ x≢zero with decZero x
... | yes x≡zero = ⊥.rec (x≢zero x≡zero)
... | no ¬x≡zero = limit-pointwise-equal _ _ (λ _ → refl)

{- # Exponentiation -}

mutual

  _^_ : Brw → Brw → Brw
  a ^ zero = one
  a ^ (succ x) = a ^ x · a
  a ^ (limit f {f↑}) with decZeroOneMany a
  ... | inl a≡zero = zero
  ... | inr (inl a≡one) = one
  ... | inr (inr one<a) = limit (λ n → a ^ (f n)) {^-preserves-increasing one<a f↑}
  a ^ (bisim f {f↑} g {g↑} (f≲g , g≲f) i) with decZeroOneMany a
  ... | inl a≡zero = zero
  ... | inr (inl a≡one) = one
  ... | inr (inr one<a) = bisim (λ n → a ^ (f n)) {^-preserves-increasing one<a f↑}
                                (λ n → a ^ (g n)) {^-preserves-increasing one<a g↑}
                                (^-preserves-≲ (one<x→x≢zero one<a) f≲g ,
                                 ^-preserves-≲ (one<x→x≢zero one<a) g≲f)
                                i
  a ^ (trunc x y p q i j) = trunc (a ^ x) (a ^ y) (λ j → (a ^ (p j))) (λ j → (a ^ (q j))) i j

  zero≢a^ : ∀ {a} → (y : Brw) → ¬ (a ≡ zero) → ¬ zero ≡ a ^ y
  zero≢a^ zero a≢zero = zero≠succ
  zero≢a^ (succ y) a≢zero p = ·-no-zero-divisors (λ p → (zero≢a^ y a≢zero) (sym p)) a≢zero (sym p)
  zero≢a^ {a} (limit f) a≢zero with decZeroOneMany a
  ... | inl a≡zero = ⊥.rec (a≢zero a≡zero)
  ... | inr (inl a≡one) = zero≠succ
  ... | inr (inr one<a) = zero≠lim
  zero≢a^ {a} (bisim f {f↑} g {g↑} (f≲g , g≲f) i) a≢zero with decZeroOneMany a
  ... | inl a≡zero = ⊥.rec (a≢zero a≡zero)
  ... | inr (inl a≡one) = zero≠succ
  ... | inr (inr one<a) =
    isProp→PathP {B = λ i → ¬ zero ≡ bisim (λ n → a ^ f n)
                                           (λ n → a ^ g n)
                                           (^-preserves-≲ (one<x→x≢zero one<a) f≲g ,
                                            ^-preserves-≲ (one<x→x≢zero one<a) g≲f) i}
                 (λ i → isProp¬ _)
                 zero≠lim
                 zero≠lim
                 i
  zero≢a^ {a} (trunc x y p q i j) a≢zero =
    isProp→SquareP {B = λ i j → ¬ zero ≡ a ^ (trunc x y p q i j)}
                   (λ i j → isProp¬ _)
                   refl
                   refl
                   (λ j → zero≢a^ (p j) a≢zero)
                   (λ j → zero≢a^ (q j) a≢zero)
                   i j

  one^y≡one : ∀ y → one ^ y ≡ one
  one^y≡one zero = refl
  one^y≡one (succ y) = zero+y≡y (one ^ y) ∙ one^y≡one y
  one^y≡one (limit f) = refl
  one^y≡one (bisim f g p i) = refl
  one^y≡one (trunc x y p q i j) =
    isProp→SquareP {B = λ i j → trunc (one ^ x) (one ^ y)
                                      (λ j₁ → one ^ p j₁) (λ j₁ → one ^ q j₁) i j
                              ≡ one}
                   (λ i j → Brw-is-set _ _)
                   refl
                   refl
                   (λ j → one^y≡one (p j))
                   (λ j → one^y≡one (q j))
                   i j

  a^-mono : {a x y : Brw} → ¬ (a ≡ zero) → x ≤ y → a ^ x ≤ a ^ y
  a^-mono a≢zero (≤-zero {y}) = zero≠x→zero<x _ (zero≢a^ y a≢zero)
  a^-mono a≢zero (≤-trans x≤z z≤y) = ≤-trans (a^-mono a≢zero x≤z) (a^-mono a≢zero z≤y)
  a^-mono {a} a≢zero (≤-succ-mono {x} {y} x≤y) = ·x-mono a (a^-mono a≢zero x≤y)
  a^-mono {a} a≢zero (≤-cocone {x} f {k = k} x≤fk) with decZeroOneMany a
  ... | inl a≡zero = ⊥.rec (a≢zero a≡zero)
  ... | inr (inl a≡one) = subst (λ z → z ≤ one) (sym (cong (_^ x) a≡one ∙ one^y≡one x)) ≤-refl
  ... | inr (inr one<a) = ≤-cocone (λ n → a ^ (f n)) {k = k} (a^-mono a≢zero x≤fk)
  a^-mono {a} a≢zero (≤-limiting f {f↑} {y} f≤y) with decZeroOneMany a
  ... | inl a≡zero = ⊥.rec (a≢zero a≡zero)
  ... | inr (inl a≡one) = subst (λ z → one ≤ z) (sym (cong (_^ y) a≡one ∙ one^y≡one y)) ≤-refl
  ... | inr (inr one<a) = ≤-limiting (λ n → a ^ (f n)) (λ k → a^-mono a≢zero (f≤y k))
  a^-mono a≢zero (≤-trunc p q i) = ≤-trunc (a^-mono a≢zero p) (a^-mono a≢zero q) i

  -- See the discussion in Line 58.
  {-# TERMINATING #-}
  ^-preserves-≲ : ∀ {a f g} → ¬ a ≡ zero → f ≲ g → ((a ^_) ∘ f) ≲ ((a ^_) ∘ g)
  ^-preserves-≲ a≢zero f≲g k = ∥-∥rec isPropPropTrunc
                                      (λ { (l , fk≤gl) → ∣ l , a^-mono a≢zero fk≤gl ∣ })
                                      (f≲g k)

  ^-preserves-increasing : ∀ {a f} → one < a → increasing f → increasing (λ n → a ^ f n)
  ^-preserves-increasing {a} {f} one<a f↑ k =
    <∘≤-in-< (subst (λ z → z < a ^ f k · a)
                    (zero+y≡y (a ^ (f k)))
                    (x·-mono-< (λ p → zero≢a^ (f k) (one<x→x≢zero one<a)  (sym p)) one<a))
             (a^-mono (one<x→x≢zero one<a) (f↑ k))

{- # Powers of ω, in particular -}

ω^ : Brw → Brw
ω^ b = ω ^ b

ω^-mono : {x y : Brw} → x ≤ y → ω^ x ≤ ω^ y
ω^-mono = a^-mono λ ω≡zero → zero≠lim (sym ω≡zero)

ω^-preserves-increasing : ∀ {f} → increasing f → increasing (λ n → ω ^ f n)
ω^-preserves-increasing f↑ = ^-preserves-increasing one<lim f↑

-- ω^ b satisfies the expected equations definitionally:

ω^zero≡one : ω^ zero ≡ one
ω^zero≡one = refl

ω^⟨sx⟩≡ω^x·ω : ∀ x → ω^ (succ x) ≡ ω^ x · ω
ω^⟨sx⟩≡ω^x·ω x = refl

ω^⟨limf⟩≡lim⟨ω^⟨fn⟩⟩ : ∀ f f↑ → ω^ (limit f {f↑}) ≡ limit (λ n → ω^ (f n))
ω^⟨limf⟩≡lim⟨ω^⟨fn⟩⟩ f f↑ = refl
