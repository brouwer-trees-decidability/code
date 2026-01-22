----------------------------------------------------------------------------------------------------
-- Correctness of arithmetic operations on Brouwer Trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Arithmetic.Correctness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)
open import Cubical.Relation.Nullary

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Code
open import BrouwerTree.Code.Results
open import BrouwerTree.Arithmetic
open import BrouwerTree.Classifiability

open import Abstract.Arithmetic _<_ _≤_ public

{- Correctness of addition -}

+-is-add : is-add _+_
+-is-add = (λ a c a-is-zero → cong (c +_) (is-zero→≡zero a-is-zero)) ,
           (λ a b c d a-is-suc-b d-is-suc-c+b →
              cong (c +_) (is-suc→≡succ a-is-suc-b) ∙ sym (is-suc→≡succ d-is-suc-c+b)) ,
           (λ a b c f f↑ a-is-limf b-is-sup-c+f →
              cong (c +_) (is-lim→≡limit {a} {f} {f↑} a-is-limf) ∙
              sym (is-sup-increasing→≡limit (x+-preserves-increasing f↑) b-is-sup-c+f))

add-is-unique : (_+'_ : Brw → Brw → Brw) → is-add _+'_ → _+_ ≡ _+'_
add-is-unique _+'_ (+'-is-add-zero , +'-is-add-suc , +'-is-add-lim) = funExt (funExt ∘ go) where
  go : (c a : Brw) → c + a ≡ c +' a
  go c = Brw-ind (λ a → c + a ≡ c +' a) (λ c → Brw-is-set _ _)
           (sym (+'-is-add-zero zero c zero-is-zero))
           (λ {a} ih →
             sym (+'-is-add-suc (succ a) a c (c + succ a)
                                (succ-is-suc a)
                                (subst (λ z → succ (c + a) is-suc-of z) ih (succ-is-suc (c + a)))))
           λ {f} {f↑} ih → let c+f↑ = x+-preserves-increasing f↑ in
             sym (+'-is-add-lim (limit f {f↑}) (limit (λ n → c + f n)) c f f↑
                                (limit-is-sup f f↑)
                                (subst (λ z → limit (λ n → c + f n) {c+f↑} is-sup-of z)
                                       (funExt ih)
                                       (limit-is-sup (λ n → c + f n) (c+f↑))))

Brw-has-unique-add : has-unique-add
Brw-has-unique-add =
  (_+_ , +-is-add) , (λ (f , p) → Σ≡Prop (isProp⟨is-add⟩ Brw-is-set) (add-is-unique f p))

open Subtraction (_+_ , +-is-add) hiding (_+_) public


{- Correctness of multiplication -}

open Multiplication (_+_ , +-is-add) hiding (_+_) public

·-is-mul : is-mul _·_
·-is-mul = (λ a c a-is-zero → cong (c ·_) (is-zero→≡zero a-is-zero) ∙
                              sym (is-zero→≡zero a-is-zero)) ,
           (λ a b c a-is-suc-b → cong (c ·_) (is-suc→≡succ a-is-suc-b)) ,
           limitCase where
  limitCase : ∀ a b c f (f↑ : is-<-increasing f) → a is-lim-of (f , f↑) →
              b is-sup-of (λ i → c · f i) → c · a ≡ b
  limitCase a b c f f↑ a-is-limf b-is-sup-c+f
    with decZero c | cong (c ·_) (is-lim→≡limit {a} {f} {f↑} a-is-limf)
  ... | yes c≡zero | _ = cong (_· a) c≡zero ∙
                         zero·y≡zero a ∙
                         sym (sup-constant b-is-sup-c+f
                                           (λ n → cong (_· f n) c≡zero ∙ zero·y≡zero (f n)))
  ... | no c≢zero | eq = eq ∙ sym (is-sup-increasing→≡limit (x·-increasing c≢zero f↑) b-is-sup-c+f)

mul-is-unique : (_·'_ : Brw → Brw → Brw) → is-mul _·'_ → _·_ ≡ _·'_
mul-is-unique _·'_ (·'-is-mul-zero , ·'-is-mul-suc , ·'-is-mul-lim) = funExt (funExt ∘ go) where
  go : (c a : Brw) → c · a ≡ c ·' a
  go c = Brw-ind (λ a → c · a ≡ c ·' a) (λ c → Brw-is-set _ _)
           (sym (·'-is-mul-zero zero c zero-is-zero))
           (λ {a} ih → sym (·'-is-mul-suc (succ a) a c (succ-is-suc a) ∙ cong (_+ c) (sym ih)))
           λ {f} {f↑} → limitCase f f↑ where
      limitCase : ∀ f f↑ → (ih : (k : ℕ) → c · f k ≡ (c ·' f k)) → c · limit f ≡ c ·' limit f
      limitCase f f↑ ih with decZero c
      ... | yes c≡zero =
              sym (·'-is-mul-lim (limit f {f↑}) zero c f f↑ (limit-is-sup f f↑)
                                 ((λ k → ≤-refl-≡ ((sym (ih k)) ∙
                                                   cong (_· f k) c≡zero ∙
                                                   zero·y≡zero (f k))) ,
                                  λ x cf≤x → ≤-zero))
      ... | no  c≢zero = let c·f↑ = x·-increasing c≢zero f↑ in
                         sym (·'-is-mul-lim (limit f {f↑}) (limit (λ n → c · f n)) c f f↑
                                            (limit-is-sup f f↑)
                                            (subst (λ z → limit (λ n → c · f n) {c·f↑} is-sup-of z)
                                                   (funExt ih)
                                                   (limit-is-sup (λ n → c · f n) c·f↑)))

Brw-has-unique-mul : has-unique-mul
Brw-has-unique-mul =
  (_·_ , ·-is-mul) , (λ (f , p) → Σ≡Prop (isProp⟨is-mul⟩ Brw-is-set) (mul-is-unique f p))


{- Correctness of exponentiation -}

open Exponentiation
  (_+_ , +-is-add)
  (_·_ , ·-is-mul)
  hiding (_·_) public

^-is-exp : ∀ c → (c ^_) is-exp-with-base c
^-is-exp c = (λ a b a-is-zero b-is-suc-a →
                cong (c ^_) (is-zero→≡zero a-is-zero) ∙
                sym ((is-suc→≡succ b-is-suc-a) ∙ cong succ (is-zero→≡zero a-is-zero))) ,
             (λ a b a-is-suc-b → cong (c ^_) (is-suc→≡succ a-is-suc-b)) ,
             limitCaseNonZero ,
             limitCaseZero
 where
  limitCaseNonZero : ∀ a b f (f↑ : is-<-increasing f) → a is-lim-of (f , f↑) →
                       ¬ (is-zero c) → b is-sup-of (λ i → c ^ f i) → c ^ a ≡ b
  limitCaseNonZero a b f f↑ a-is-limf c-nonzero b-is-sup-c^f
    with decZeroOneMany c | cong (c ^_) (is-lim→≡limit {a} {f} {f↑} a-is-limf)
  limitCaseNonZero a b f f↑ a-is-limf c-nonzero b-is-sup-c^f  | inl c≡zero | eq
    = ⊥.rec (c-nonzero (subst is-zero (sym c≡zero) λ _ → ≤-zero))
  limitCaseNonZero a b f f↑ a-is-limf c-nonzero b-is-sup-c^f | inr (inl c≡one) | eq with decZero c
  limitCaseNonZero a b f f↑ a-is-limf c-nonzero b-is-sup-c^f | inr (inl c≡one) | eq | yes c≡zero
    = ⊥.rec (zero≠succ (sym c≡zero ∙ c≡one))
  limitCaseNonZero a b f f↑ a-is-limf c-nonzero b-is-sup-c^f | inr (inl c≡one) | eq | no c≢zero
    = eq ∙ sym (sup-constant b-is-sup-c^f λ n → cong (_^ f n) c≡one ∙ one^y≡one (f n))
  limitCaseNonZero a b f f↑ a-is-limf c-nonzero b-is-sup-c^f | inr (inr c>one) | eq
    = eq ∙ sym (is-sup-increasing→≡limit (^-preserves-increasing c>one f↑) b-is-sup-c^f)
  limitCaseZero : ∀ a f f↑ → a is-lim-of (f , f↑) → is-zero c → c ^ a ≡ c
  limitCaseZero a f f↑ a-is-sup-of-f c-is-zero = subst (λ x → x ^ a ≡ x) zero≡c zero^a≡zero
   where
    zero≡c : zero ≡ c
    zero≡c = sym (is-zero→≡zero c-is-zero)
    zero<a : zero < a
    zero<a = (<∘≤-in-< (≤∘<-in-< ≤-zero (f↑ 0)) (fst a-is-sup-of-f 1))
    zero^a≡zero : zero ^ a ≡ zero
    zero^a≡zero = Brw-ind (λ x → zero < x → zero ^ x ≡ zero)
                          (λ _ → isPropΠ λ _ → Brw-is-set _ _)
                          (λ z<z → ⊥.rec (<-irreflexive zero z<z))
                          (λ _ _ → refl)
                          (λ _ _ → refl)
                          a zero<a

exp-is-unique : ∀ c → (c^'_ : Brw → Brw) → (c^'_) is-exp-with-base c → (c ^_) ≡ (c^'_)
exp-is-unique c c^'_ (c^'-exp-zero , c^'-exp-suc , c^'-exp-lim-nz , c^'-exp-lim-z) = funExt go
 where
  go : (a : Brw) → c ^ a ≡ c^' a
  go = Brw-ind (λ a → c ^ a ≡ c^' a)
               (λ c → Brw-is-set _ _)
               (sym (c^'-exp-zero zero one zero-is-zero (succ-is-suc zero)))
               (λ {a} ih → sym (c^'-exp-suc (succ a) a (succ-is-suc a) ∙ cong (_· c) (sym ih)))
               (λ {f} {f↑} → limitCase f f↑)
   where
    limitCase : ∀ f f↑ → ((k : ℕ) → c ^ f k ≡ (c^' f k)) → c ^ limit f {f↑} ≡ (c^' limit f {f↑})
    limitCase f f↑ ih with decZeroOneMany c
    ... | inl c≡zero
      = sym (subst (c^' limit f ≡_) c≡zero
                   (c^'-exp-lim-z (limit f {f↑}) f f↑ (limit-is-sup f f↑)
                                  (subst is-zero (sym c≡zero) zero-is-zero)))
    ... | inr (inl c≡one)
      = sym (c^'-exp-lim-nz (limit f {f↑}) one f f↑ (limit-is-sup f f↑)
                            (λ h → succ≰zero (subst (_≤ zero) c≡one (h zero)))
                            ((λ k → ≤-refl-≡ (sym (ih k) ∙ cong (_^ f k) c≡one ∙ one^y≡one (f k))) ,
                             (λ x c^'f≤x → ≤-trans (≤-refl-≡ (sym (sym (ih 17) ∙
                                                                   cong (_^ f 17) c≡one ∙
                                                                   one^y≡one (f 17))))
                                                   (c^'f≤x 17))))
    ... | inr (inr c>one)
      = let c·f↑ = ^-preserves-increasing c>one f↑ in
        sym (c^'-exp-lim-nz (limit f {f↑}) (limit (λ n → c ^ f n)) f f↑
                            (limit-is-sup f f↑) (λ h → x≮zero (<∘≤-in-< c>one (h zero)))
                            ((subst (λ z → limit (λ n → c ^ f n) {c·f↑} is-sup-of z)
                                    (funExt ih)
                                    (limit-is-sup (λ n → c ^ f n) c·f↑))))

Brw-has-unique-exp : has-unique-exp
Brw-has-unique-exp c =
  (c ^_ , ^-is-exp c) , (λ (f , p) → Σ≡Prop (isProp⟨is-exp⟩ Brw-is-set c)
                                                  (exp-is-unique c f p))
