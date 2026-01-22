----------------------------------------------------------------------------------------------------
-- Brouwer trees as a quotient inductive-inductive type
----------------------------------------------------------------------------------------------------

{- Brouwer trees consisting of zero, succ, and limits of strictly
   increasing sequences.  The path constructor of the ordinal type
   says that bisimilar sequences give equal limits.  The type of
   Brouwer trees with this definition will not be a set automatically.
   Therefore, a truncation constructor is added. -}

{-# OPTIONS --erased-cubical --erasure --guardedness --safe #-}

module BrouwerTree.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

import Simulations
  renaming (_simulated-by_ to _≲_ ; _bisimilar-to_ to _≈_)


{- Quotient inductive-inductive type of Brouwer trees -}

mutual
  data Brw : Type
  data _≤_ : Brw → Brw → Type

  open Simulations Brw _≤_ public

  data Brw where
    zero  : Brw
    succ  : Brw → Brw
    limit : (f : ℕ → Brw) → {f↑ : increasing f} → Brw
    bisim : ∀ f {f↑} g {g↑} →
            f ≈ g →
            limit f {f↑} ≡ limit g {g↑}
    trunc : (x y : Brw) → (p q : x ≡ y) → p ≡ q

  data _≤_ where
    ≤-zero      : ∀ {x} → zero ≤ x
    ≤-trans     : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-succ-mono : ∀ {x y} → x ≤ y → succ x ≤ succ y
    ≤-cocone    : ∀ {x} f {f↑ k} → (x ≤ f k) → (x ≤ limit f {f↑})
    ≤-limiting  : ∀ f {f↑ x} → ((k : ℕ) → f k ≤ x) → limit f {f↑} ≤ x
    ≤-trunc     : ∀ {x y} → (p q : x ≤ y) → p ≡ q

  _<_ : Brw → Brw → Type
  x < y = succ x ≤ y

  increasing : (ℕ → Brw) → Type
  increasing f = ∀ k → f k < f (suc k)
{-
≤-trans : ∀ (x y z : Brw) → x ≤ y → y ≤ z → x ≤ z
≤-trans zero y z p ≤-zero = ≤-zero
≤-trans (succ x) y z p (≤-zero)  = {!p!} -- why I cant write zero instead of y?
≤-trans (limit f) y z p ≤-zero = {!!}
≤-trans (bisim f g x i) y z p ≤-zero = {!!}
≤-trans (trunc x x₁ p₁ q i i₁) y z p ≤-zero = {!!}
≤-trans zero y z p (≤-succ-mono q) = {!!}
≤-trans (succ x) y z p (≤-succ-mono q) = {!!}
≤-trans (limit f) y z p (≤-succ-mono q) = {!!}
≤-trans (bisim f g x i) y z p (≤-succ-mono q) = {!!}
≤-trans (trunc x x₁ p₁ q₁ i i₁) y z p (≤-succ-mono q) = {!!}
≤-trans x y z p (≤-cocone f q) = {!!}
≤-trans x y z p (≤-limiting f x₁) = {!!}
≤-trans x y z p (≤-trunc q q₁ i) = {!!}
-}

one = succ zero

ι : ℕ → Brw
ι zero = zero
ι (suc x) = succ (ι x)

ι-increasing : increasing ι
ι-increasing zero = ≤-succ-mono ≤-zero
ι-increasing (suc k) = ≤-succ-mono (ι-increasing k)

ω = limit ι {ι-increasing}

isProp→PathP' : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → isProp (B i))
               → (b0 : B i0) (b1 : B i1)
               → PathP B b0 b1
isProp→PathP' hB b0 b1 = toPathP' (hB _ _ _) where
  toPathP' : ∀ {ℓ} → {A : I → Type ℓ} {x : A i0} {y : A i1} →
           transport (λ i → A i) x ≡ y → PathP A x y
  toPathP' {A = A} {x} {y} p i
    = hcomp (λ j → λ { (i = i0) → x
                     ; (i = i1) → p j })
            (transp (λ j → A (i ∧ j)) (~ i) x)

isProp→SquareP' : ∀ {ℓ} {B : I → I → Type ℓ} → ((i j : I) → isProp (B i j))
             → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
             → (r : PathP (λ j → B j i0) a c) (s : PathP (λ j → B j i1) b d)
             → (t : PathP (λ j → B i0 j) a b) (u : PathP (λ j → B i1 j) c d)
             → SquareP B t u r s
isProp→SquareP' {B = B} isPropB {a = a} r s t u i j =
  hcomp (λ { k (i = i0) → isPropB i0 j (base i0 j) (t j) k
           ; k (i = i1) → isPropB i1 j (base i1 j) (u j) k
           ; k (j = i0) → isPropB i i0 (base i i0) (r i) k
           ; k (j = i1) → isPropB i i1 (base i i1) (s i) k
        }) (base i j) where
    base : (i j : I) → B i j
    base i j = transp (λ k → B (i ∧ k) (j ∧ k)) i0 a


Brw-ind : ∀ {a} →
            (P : Brw → Type a) →
            (P-prop : (x : Brw) → isProp (P x)) →
            (z : P zero) →
            (s : {x : Brw} → P x → P (succ x)) →
            (l : ∀ {f f↑} → ((k : ℕ) → P (f k)) → P (limit f {f↑})) →
            (x : Brw) → P x
Brw-ind P isProp⟨P⟩ z s l zero = z
Brw-ind P isProp⟨P⟩ z s l (succ x) = s (Brw-ind P isProp⟨P⟩ z s l x)
Brw-ind P isProp⟨P⟩ z s l (limit f {f↑}) = l λ k → Brw-ind P isProp⟨P⟩ z s l (f k)
Brw-ind P isProp⟨P⟩ z s l (bisim f {f↑} g {g↑} f∼g i) =
  isProp→PathP' (λ j → isProp⟨P⟩ (bisim f g f∼g j))
                (l λ k → Brw-ind P isProp⟨P⟩ z s l (f k))
                (l λ k → Brw-ind P isProp⟨P⟩ z s l (g k)) i
Brw-ind P isProp⟨P⟩ z s l (trunc x y p q i j) =
  isProp→SquareP' (λ i j → isProp⟨P⟩ (trunc x y p q i j))
                  (λ j → Brw-ind P isProp⟨P⟩ z s l x)
                  (λ j → Brw-ind P isProp⟨P⟩ z s l y)
                  (λ j → Brw-ind P isProp⟨P⟩ z s l (p j))
                 (λ j → Brw-ind P isProp⟨P⟩ z s l (q j)) i j

infix 4 _≤_
