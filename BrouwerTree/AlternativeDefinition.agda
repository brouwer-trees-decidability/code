----------------------------------------------------------------------------------------------------
-- An alternative definition of Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

{- This file presents an alternative definition of Brouwer trees.
   The difference to our main definition of Brouwer trees is:
   * The main definition uses a constructors
     `bisim` and `trunc` which ensure that weakly bisimilar
     sequences have equal limits, and that the type of
     Brouwer trees is a set.
   * This alternative definition instead directly uses a
     constructor `antisym`.
   Here, we show that the two definitions are equivalent.
-}

module BrouwerTree.AlternativeDefinition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
  using (HSeparated; HSeparated→isSet)

open import PropTrunc

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Code
open import BrouwerTree.Code.Results

{- The alternative definition -}

mutual
  data Brw' : Type where
    zero'    : Brw'
    succ'    : Brw' -> Brw'
    limit'   : (f : ℕ -> Brw') {f↑ : increasing' f} -> Brw'
    antisym' : ∀ {x y} -> x ≤' y -> y ≤' x -> x ≡ y

  data _≤'_ : Brw' -> Brw' -> Type where
    ≤-zero'    : ∀ {x} → zero' ≤' x
    ≤-trans'   : ∀ {x y z} -> x ≤' y -> y ≤' z -> x ≤' z
    succ-mono' : ∀ {x y} -> x ≤' y -> succ' x ≤' succ' y
    cocone'    : ∀ f {f↑} k {x} -> x ≤' f k -> x ≤' limit' f {f↑}
    limiting'  : ∀ f {f↑ x} -> ((k : ℕ) -> f k ≤' x) -> limit' f {f↑} ≤' x
    ≤-trunc'   : ∀ {x y} -> isProp (x ≤' y)

  _<'_ : Brw' -> Brw' -> Type
  x <' y = succ' x ≤' y

  increasing' : (ℕ → Brw') -> Type
  increasing' f = ∀ k → f k <' f (suc k)

Brw'-ind : ∀ {a} →
             (P : Brw' → Type a) →
             (P-prop : (x : Brw') → isProp (P x)) →
             (z : P zero') →
             (s : {x : Brw'} → P x → P (succ' x)) →
             (l : ∀ {f f↑} → ((k : ℕ) → P (f k)) → P (limit' f {f↑})) →
             (x : Brw') → P x
Brw'-ind P isProp⟨P⟩ z s l zero' = z
Brw'-ind P isProp⟨P⟩ z s l (succ' x) = s (Brw'-ind P isProp⟨P⟩ z s l x)
Brw'-ind P isProp⟨P⟩ z s l (limit' f {f↑}) = l λ k → Brw'-ind P isProp⟨P⟩ z s l (f k)
Brw'-ind P isProp⟨P⟩ z s l (antisym' {x} {y} p q i) =
  isProp→PathP (λ j → isProp⟨P⟩ (antisym' p q j))
               (Brw'-ind P isProp⟨P⟩ z s l x)
               (Brw'-ind P isProp⟨P⟩ z s l y) i

≤'-refl : ∀ {x} → x ≤' x
≤'-refl {zero'} = ≤-zero'
≤'-refl {succ' x} = succ-mono' (≤'-refl {x})
≤'-refl {limit' f {f↑}} = limiting' f {f↑} λ k → cocone' f {f↑} k {f k} (≤'-refl {f k})
≤'-refl {antisym' {x} {y} p q i} =
  isProp→PathP {B = λ i → antisym' p q i ≤' antisym' p q i}
               (λ _ → ≤-trunc')
               (≤'-refl {x})
               (≤'-refl {y}) i

≤'-refl-≡ : ∀ {x y} → x ≡ y → x ≤' y
≤'-refl-≡ {x} {y} x≡y = subst (λ z → z ≤' y) (sym x≡y) ≤'-refl

Brw'-hSeparated : HSeparated Brw'
Brw'-hSeparated x y ∣x≡y∣ = antisym' x≤y y≤x
  where
  x≤y×y≤x =
    ∥-∥rec
      (isProp× ≤-trunc' ≤-trunc')
      (λ x≡y → subst (λ z → x ≤' z) x≡y ≤'-refl , subst (λ z → z ≤' x) x≡y ≤'-refl)
      (fromLib∥-∥ ∣x≡y∣)
  x≤y = fst x≤y×y≤x
  y≤x = snd x≤y×y≤x

Brw'-is-set : isSet Brw'
Brw'-is-set = HSeparated→isSet Brw'-hSeparated


open import Simulations Brw' _≤'_
  renaming (_simulated-by_ to _≲'_ ; _bisimilar-to_ to _≈'_)

bisim→≤' : ∀ {f f↑ g g↑} → f ≲' g → limit' f {f↑} ≤' limit' g {g↑}
bisim→≤' {f} {f↑} {g} {g↑} f≲g =
  limiting' f {x = limit' g} (λ k → ∥-∥rec {A = Σ[ n ∈ ℕ ] f k ≤' g n}
                                           {P = f k ≤' limit' g}
                                           ≤-trunc'
                                           (λ {(n , fk≤'gn) → cocone' g n {f k} fk≤'gn})
                                           (f≲g k))

bisim' : ∀ {f f↑ g g↑} → f ≈' g → limit' f {f↑} ≡ limit' g {g↑}
bisim' {f} {f↑} {g} {g↑} (f≲'g , g≲'f) = antisym' (bisim→≤' f≲'g) (bisim→≤' g≲'f)

{- Maps back and forth -}

mutual
  Brw→Brw' : Brw → Brw'
  Brw→Brw' zero = zero'
  Brw→Brw' (succ x) = succ' (Brw→Brw' x)
  Brw→Brw' (limit f {f↑}) = limit' (Brw→Brw' ∘ f)
                                   {λ k → Brw→Brw'-mono {succ (f k)} {f (suc k)} (f↑ k)}
  Brw→Brw' (bisim f {f↑} g {g↑} (f≲g , g≲f) i) =
    bisim' {f↑ = λ k → Brw→Brw'-mono {succ (f k)} {f (suc k)} (f↑ k)}
           {g↑ = λ k → Brw→Brw'-mono {succ (g k)} {g (suc k)} (g↑ k)}
           (Brw→Brw'-pres-bisim f≲g  , Brw→Brw'-pres-bisim g≲f) i
  Brw→Brw' (trunc x y p q i j) = isSet→SquareP {A = λ _ _ → Brw'} (λ _ _ → Brw'-is-set)
                                                (λ j → Brw→Brw' (p j))
                                                (λ j → Brw→Brw' (q j))
                                                refl
                                                refl i j

  Brw→Brw'-mono : ∀ {x y} → x ≤ y → (Brw→Brw' x ≤' Brw→Brw' y)
  Brw→Brw'-mono {.zero} {y} ≤-zero = ≤-zero'
  Brw→Brw'-mono (≤-trans {x} {y} {z} x≤y y≤z) = ≤-trans' (Brw→Brw'-mono x≤y) (Brw→Brw'-mono y≤z)
  Brw→Brw'-mono {.(succ x)} {.(succ y)} (≤-succ-mono {x} {y} x≤y) = succ-mono' (Brw→Brw'-mono x≤y)
  Brw→Brw'-mono {x} {.(limit f)} (≤-cocone f {k = k} x≤y) = cocone' (Brw→Brw' ∘ f) k
                                                                    (Brw→Brw'-mono x≤y)
  Brw→Brw'-mono {.(limit f)} {y} (≤-limiting f f≤y) = limiting' (Brw→Brw' ∘ f) (Brw→Brw'-mono ∘ f≤y)
  Brw→Brw'-mono {x} {y} (≤-trunc p q i) = ≤-trunc' (Brw→Brw'-mono p) (Brw→Brw'-mono q) i

  -- Agda does not see that the recursive call on `fk≤gn` is structurally smaller,
  -- because it has been uncovered under the propositional truncation. In the
  -- "official" induction principle, we instead get a family of truncated inductive hypothesis,
  -- and here we can uncover the k-th one because we are proving a proposition.
  -- To work around this, we mark the definition as terminating.
  {-# TERMINATING #-}
  Brw→Brw'-pres-bisim : ∀ {f g} → f ≲ g → (Brw→Brw' ∘ f) ≲' (Brw→Brw' ∘ g)
  Brw→Brw'-pres-bisim {f} {g} f≲g =
    λ k → ∥-∥rec {A = Σ[ n ∈ ℕ ] f k ≤ g n}
                 {P = ∥ Σ[ n ∈ ℕ ] Brw→Brw' (f k) ≤' Brw→Brw' (g n) ∥}
                 isPropPropTrunc
                 (λ {(n , fk≤gn) → ∣(n , Brw→Brw'-mono fk≤gn)∣})
                 (f≲g k)

mutual
  Brw'→Brw : Brw' → Brw
  Brw'→Brw zero' = zero
  Brw'→Brw (succ' x) = succ (Brw'→Brw x)
  Brw'→Brw (limit' f {f↑}) = limit (λ n → Brw'→Brw (f n)) {λ k → Brw'→Brw-mono (f↑ k)}
  Brw'→Brw (antisym' p q i) = ≤-antisym (Brw'→Brw-mono p) (Brw'→Brw-mono q) i

  Brw'→Brw-mono : ∀ {x y} → x ≤' y → (Brw'→Brw x ≤ Brw'→Brw y)
  Brw'→Brw-mono ≤-zero' = ≤-zero
  Brw'→Brw-mono (≤-trans' x≤z z≤y) = ≤-trans (Brw'→Brw-mono x≤z) (Brw'→Brw-mono z≤y)
  Brw'→Brw-mono (succ-mono' x≤y) = ≤-succ-mono (Brw'→Brw-mono x≤y)
  Brw'→Brw-mono (cocone' f k x≤fk) = ≤-cocone (λ n → Brw'→Brw (f n)) {k = k} (Brw'→Brw-mono x≤fk)
  Brw'→Brw-mono (limiting' f f≤y) = ≤-limiting (λ n → Brw'→Brw (f n)) (λ k → Brw'→Brw-mono (f≤y k))
  Brw'→Brw-mono (≤-trunc' p q i) = ≤-trunc (Brw'→Brw-mono p) (Brw'→Brw-mono q) i

{- Identities are straightforward. -}

right-identity : (x : Brw') → Brw→Brw' (Brw'→Brw x) ≡ x
right-identity = Brw'-ind (λ x → Brw→Brw' (Brw'→Brw x) ≡ x)
                          (λ c → Brw'-is-set _ _)
                          refl
                          (λ {x} ih → cong succ' ih)
                          (λ {f} {f↑} ih → bisim' ((λ k → ∣ k , ≤'-refl-≡ (ih k) ∣) ,
                                                   (λ k → ∣ k , ≤'-refl-≡ (sym (ih k)) ∣)))

left-identity : (x : Brw) → Brw'→Brw (Brw→Brw' x) ≡ x
left-identity = Brw-ind (λ x → Brw'→Brw (Brw→Brw' x) ≡ x)
                        (λ c → Brw-is-set _ _)
                        refl
                        (λ {x} ih → cong succ ih)
                        (λ {f} {f↑} ih → bisim (λ n → Brw'→Brw (Brw→Brw' (f n))) f
                                               ((λ k → ∣ k , ≤-refl-≡ (ih k) ∣) ,
                                                (λ k → ∣ k , ≤-refl-≡ (sym (ih k)) ∣)))

{- Hence Brw and Brw' are equivalent. -}

Brw≃Brw' : Brw ≃ Brw'
Brw≃Brw' = isoToEquiv (iso Brw→Brw'  Brw'→Brw right-identity left-identity)
