----------------------------------------------------------------------------------------------------
-- Some properties of Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --erasure --guardedness --safe #-}

module BrouwerTree.Properties.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import PropTrunc

open import BrouwerTree.Base

{- ≤ is reflexive -}

≤-refl : ∀ {x} → x ≤ x
≤-refl {x} =
  Brw-ind (λ x → x ≤ x)
          (λ x → ≤-trunc)
          ≤-zero
          ≤-succ-mono
          (λ {f f↑} fk≤fk → ≤-limiting f {f↑ = f↑} {x = limit f {f↑}} λ k →
             ≤-cocone f {f↑} {k} (fk≤fk k))
          x

{- simplified cocone formulation -}

≤-cocone-simple : ∀ f {f↑} {k} → f k ≤ limit f {f↑}
≤-cocone-simple f {f↑} {k} = ≤-cocone f {f↑} {k} ≤-refl

{- Agda's standard notational trick -}

_≤⟨_⟩_ : ∀ {y z} → (x : Brw) → (x ≤ y) → (y ≤ z) → (x ≤ z)
x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

_≤∎ : (x : Brw) → x ≤ x
_ ≤∎ = ≤-refl

infixr  0 _≤⟨_⟩_
infix   1 _≤∎

{- simple lemmas about succ and ≤ -}

<-succ-incr-simple : ∀ {x} → x < succ x
<-succ-incr-simple = ≤-refl

≤-succ-incr-simple : ∀ {x} → x ≤ succ x
≤-succ-incr-simple {x} =
  Brw-ind (λ x → x ≤ succ x)
          (λ _ → ≤-trunc)
          ≤-zero
          ≤-succ-mono
          (λ {f} {f↑} f≤sf → ≤-limiting f {f↑} λ k →
             f k            ≤⟨ f≤sf k ⟩
             succ (f k)     ≤⟨ ≤-succ-mono (≤-cocone-simple f) ⟩
             succ (limit f) ≤∎)
          x

≤-succ-incr : ∀ {x y} → x ≤ y → x ≤ succ y
≤-succ-incr {x} {y} x≤y = ≤-trans x≤y ≤-succ-incr-simple

