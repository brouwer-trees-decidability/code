----------------------------------------------------------------------------------------------------
-- Characterisation of ≤ for Brouwer trees via a family Code
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Code where

{- This module characterizes the inequality ≤ of Brouwer ordinal trees.
   We define a family
     Code : Brw → Brw → Type,
   valued in propositions, and show that
     x ≤ y  ↔  Code x y.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

-- open import Cubical.Relation.Nullary

open import PropTrunc

open import BrouwerTree.Base
open import BrouwerTree.Properties

mutual

  {- ## Code
     The main object of interest in this construction are Code and Code',
     as well as the correctness properties of Code (introduced later). -}

  Code' : Brw → Brw → hProp ℓ-zero

  Code : Brw → Brw → Type ℓ-zero
  Code x y = typ (Code' x y)

  isPropCode : (x y : Brw) -> isProp (Code x y)
  isPropCode x y = str (Code' x y)

  _simulated-byᶜ_ : (f g : ℕ → Brw) → Type _
  f simulated-byᶜ g = ∀ k → ∥ Σ[ n ∈ ℕ ] Code (f k) (g n) ∥

  _bisimilar-toᶜ_ : (f g : ℕ → Brw) → Type _
  f bisimilar-toᶜ g = f simulated-byᶜ g × f simulated-byᶜ f

  -- Code is defined by induction on the first, then on the second argument.

  -- case: first argument is zero
  Code' zero y = Unit , isPropUnit

  -- case: first argument is a successor
  Code' (succ x) zero = ⊥ , isProp⊥
  Code' (succ x) (succ y) = Code' x y
  Code' (succ x) (limit f) = ∥ (Σ[ n ∈ ℕ ] Code (succ x) (f n)) ∥ , isPropPropTrunc
  Code' (succ x) (bisim f {f↑} g {g↑} (f≲g , g≲f) i) =
    Σ≡Prop (λ _ → isPropIsProp)
           {u = Code' (succ x) (limit f {f↑})}
           {v = Code' (succ x) (limit g {g↑})}
           (hPropExt isPropPropTrunc isPropPropTrunc
                     (∥-∥rec {A = Σ[ n ∈ ℕ ] (Code (succ x) (f n))}
                             {P = ∥ Σ[ n ∈ ℕ ] (Code (succ x) (g n)) ∥}
                             isPropPropTrunc
                             (λ {(k , sx≤fk) →
                                ∥-∥rec isPropPropTrunc
                                       (λ { (l , fk≤gl) → ∣ l , Code-trans {succ x} {f k} {g l}
                                                                           sx≤fk (≤→Code fk≤gl) ∣ })
                                       (f≲g k) }))
                     (∥-∥rec {A = Σ[ n ∈ ℕ ] (Code (succ x) (g n))}
                             {P = ∥ Σ[ n ∈ ℕ ] (Code (succ x) (f n)) ∥}
                             isPropPropTrunc
                             (λ {(k , sx≤gk) →
                                ∥-∥rec isPropPropTrunc
                                       (λ { (l , gk≤fl) → ∣ l , Code-trans {succ x} {g k} {f l}
                                                                           sx≤gk (≤→Code gk≤fl) ∣ })
                                       (g≲f k) })))
                     i
  Code' (succ x) (trunc y₁ y₂ p q i j) =
    isSet→SquareP {A = λ _ _ → hProp ℓ-zero}
                  (λ _ _ → isSetHProp)
                  (λ j → Code' (succ x) (p j))
                  (λ j → Code' (succ x) (q j))
                  refl
                  refl
                  i j

  -- case: first argument is a limit
  Code' (limit f {f↑}) zero = ⊥ , isProp⊥
  Code' (limit f {f↑}) (succ y) = ((k : ℕ) -> Code (f k) (succ y)) ,
                                  isPropΠ (λ k → isPropCode (f k) (succ y))
  Code' (limit f {f↑}) (limit g {g↑}) = f simulated-byᶜ g ,
                                        isPropΠ λ n → isPropPropTrunc
  Code' (limit f {f↑}) (bisim g {g↑} h {h↑} (g≲h , h≲g) i) =
    Σ≡Prop (λ _ → isPropIsProp)
           {u = Code' (limit f {f↑}) (limit g {g↑})}
           {v = Code' (limit f {f↑}) (limit h {h↑})}
           (hPropExt (isPropΠ (λ z → isPropPropTrunc)) (isPropΠ (λ z → isPropPropTrunc))
                     (λ f≲g k → (∥-∥rec {A = Σ[ n ∈ ℕ ] Code (f k) (g n)}
                                        {P = ∥ Σ[ m ∈ ℕ ] Code (f k) (h m) ∥}
                                        isPropPropTrunc
                                        (λ {(n , c-fk≤gn) →
                                           ∥-∥rec isPropPropTrunc
                                                  (λ { (l , gn≤hl) →
                                                    ∣ l , Code-trans {f k} c-fk≤gn
                                                                           (≤→Code gn≤hl) ∣ })
                                           (g≲h n) })
                                        (f≲g k)))
                     (λ f≲h k → (∥-∥rec {A = Σ[ n ∈ ℕ ] Code (f k) (h n)}
                                        {P = ∥ Σ[ m ∈ ℕ ] Code (f k) (g m) ∥}
                                        isPropPropTrunc
                                        (λ {(n , c-fk≤hn) →
                                           ∥-∥rec isPropPropTrunc
                                                  (λ { (l , hn≤gl) →
                                                    ∣ l , Code-trans {f k} c-fk≤hn
                                                                           (≤→Code hn≤gl) ∣ })
                                           (h≲g n) })
                                        (f≲h k))))
                     i
  Code' (limit f {f↑}) (trunc x y p q i j) =
    isSet→SquareP {A = λ _ _ → hProp ℓ-zero}
                  (λ _ _ → isSetHProp)
                  (λ j → Code' (limit f {f↑}) (p j))
                  (λ j → Code' (limit f {f↑}) (q j))
                  refl
                  refl
                  i j

  -- case: first argument is the bisim constructor
  Code' (bisim f g x i) zero = ⊥ , isProp⊥
  Code' (bisim f {f↑} g {g↑} (f≲g , g≲f) i) (succ y) =
    Σ≡Prop (λ _ → isPropIsProp)
           {u = Code' (limit f {f↑}) (succ y)}
           {v = Code' (limit g {g↑}) (succ y)}
           (hPropExt (isPropΠ (λ k → isPropCode (f k) (succ y)))
                     (isPropΠ (λ k → isPropCode (g k) (succ y)))
                     (λ fk<sy k → ∥-∥rec (isPropCode (g k) (succ y))
                                         (λ { (l , gk≤fl) → Code-trans {g k} (≤→Code gk≤fl)
                                                                             (fk<sy l) }) (g≲f k))
                     (λ gk<sy k → ∥-∥rec (isPropCode (f k) (succ y))
                                         (λ { (l , fk≤gl) → Code-trans {f k} (≤→Code fk≤gl)
                                                                             (gk<sy l) }) (f≲g k)))
           i

  -- symmetric to the limit-bisim case
  Code' (bisim f {f↑} g {g↑} (f≲g , g≲f) i) (limit h {h↑}) =
    Σ≡Prop (λ _ → isPropIsProp)
           {u = Code' (limit f {f↑}) (limit h {h↑})}
           {v = Code' (limit g {g↑}) (limit h {h↑})}
           (hPropExt (isPropΠ λ _ → isPropPropTrunc)
                     (isPropΠ λ _ → isPropPropTrunc)
                     (λ f≲h k → ∥-∥rec isPropPropTrunc
                                       (λ { (l , gk≤fl) →
                                         ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (f l) (h n)}
                                               {P = ∥ Σ[ m ∈ ℕ ] Code (g k) (h m) ∥}
                                               isPropPropTrunc
                                               (λ { (n , c-fl≤hn) →
                                                 ∣ n , Code-trans {g k} (≤→Code gk≤fl) c-fl≤hn ∣ })
                                               (f≲h l) })
                                       (g≲f k))
                    (λ g≲h k → ∥-∥rec isPropPropTrunc
                                      (λ { (l , fk≤gl) →
                                         ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (g l) (h n)}
                                               {P = ∥ Σ[ m ∈ ℕ ] Code (f k) (h m) ∥}
                                               isPropPropTrunc
                                               (λ { (n , c-gl≤hn) →
                                                 ∣ n , Code-trans {f k} (≤→Code fk≤gl) c-gl≤hn ∣ })
                                               (g≲h l) })
                                      (f≲g k)))
           i

  -- bisim-bisim and bisim-trunc
  Code' (bisim f {f↑} g {g↑} f-g-bisim i) (bisim h {h↑} k {k↑} h-k-bisim j) =
    isSet→SquareP (λ i j → isSetHProp)
                  (λ j → Code' (limit f {f↑}) (bisim h {h↑} k {k↑} h-k-bisim j))
                  (λ j → Code' (limit g {g↑}) (bisim h {h↑} k {k↑} h-k-bisim j))
                  (λ i → Code' (bisim f {f↑} g {g↑} f-g-bisim i) (limit h {h↑}))
                  (λ i → Code' (bisim f {f↑} g {g↑} f-g-bisim i) (limit k {k↑})) i j
  Code' (bisim f {f↑} g {g↑} f≈g i) (trunc x y p q j j') =
    isGroupoid→isGroupoid' (isSet→isGroupoid isSetHProp)
                           (λ j j' → Code' (limit f {f↑})  (trunc x y p q j j'))
                           (λ j j' → Code' (limit g {g↑})  (trunc x y p q j j'))
                           (λ i j → Code' (bisim f {f↑} g {g↑} f≈g i) (p j))
                           (λ i j → Code' (bisim f {f↑} g {g↑} f≈g i) (q j))
                           (λ i j → Code' (bisim f {f↑} g {g↑} f≈g i) x)
                           (λ i j → Code' (bisim f {f↑} g {g↑} f≈g i) y) i j j'

  -- case: first argument is the set-truncation constructor
  Code' (trunc x₁ x₂ p q i j) y =
    isSet→SquareP {A = λ _ _ → hProp ℓ-zero}
                  (λ _ _ → isSetHProp)
                  (λ j → Code' (p j) y)
                  (λ j → Code' (q j) y)
                  refl
                  refl i j


  {- ## Transitivity of Code.
     This needs to be proved mutually. There probably is no elegant way of doing this.
     We simply pattern match on everything and power through. -}
  Code-trans : ∀ {x y z} → Code x y → Code y z → Code x z
  Code-trans {zero} {y} {z} c-x≤y c-y≤z = tt
  Code-trans {succ x} {succ y} {succ z} c-sx≤sy c-sy≤sz = Code-trans {x} {y} {z} c-sx≤sy c-sy≤sz
  Code-trans {succ x} {succ y} {limit f} c-sx≤sy =
    ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (succ y) (f n)}
          {P = ∥ Σ[ n ∈ ℕ ] Code (succ x) (f n) ∥}
          isPropPropTrunc
          λ {(n , c-sy≤fn) → ∣ n , Code-trans {succ x} {succ y} {f n} c-sx≤sy c-sy≤fn ∣}
  Code-trans {succ x} {succ y} {bisim f {f↑} g {g↑} f∼g i} c-x≤y =
    isProp→PathP {B = λ i → Code (succ y) (bisim f {f↑} g {g↑} f∼g i)
                          → Code (succ x) (bisim f {f↑} g {g↑} f∼g i)}
                 (λ i → isProp→ (isPropCode (succ x) (bisim f {f↑} g {g↑} f∼g i)))
                 (Code-trans {succ x} {succ y} {limit f {f↑}} c-x≤y)
                 (Code-trans {succ x} {succ y} {limit g {g↑}} c-x≤y)
                 i
  Code-trans {succ x} {succ y} {trunc z₁ z₂ p q i j} c-x≤y =
    isProp→SquareP {B = λ i j → Code (succ y) (trunc z₁ z₂ p q i j)
                              → Code (succ x) (trunc z₁ z₂ p q i j)}
                   (λ i j → isProp→ (isPropCode (succ x) (trunc z₁ z₂ p q i j)))
                   refl
                   refl
                   (λ j → Code-trans {succ x} {succ y} {p j} c-x≤y)
                   (λ j → Code-trans {succ x} {succ y} {q j} c-x≤y)
                   i j
  Code-trans {succ x} {limit f} {succ z} c-sx≤⊔f c-⊔f≤sz =
    ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (succ x) (f n)}
           {P = Code x z}
           (isPropCode x z)
           (λ {(n , c-sx≤fn) → Code-trans {succ x} {f n} {succ z} c-sx≤fn (c-⊔f≤sz n)})
           c-sx≤⊔f
  Code-trans {succ x} {limit f} {limit g} =
     ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (succ x) (f n)}
           {P = f simulated-byᶜ g → ∥ Σ[ n ∈ ℕ ] Code (succ x) (g n) ∥}
           (isProp→  isPropPropTrunc)
           λ { (n , c-sx≤fn) f-g-∥csim∥ →
             ∥-∥rec {A = Σ ℕ (λ m → Code (f n) (g m)) }
                   {P =  ∥ Σ ℕ (λ m → Code (succ x) (g m)) ∥}
                   isPropPropTrunc
                   (λ { (m , c-fn≤gm) → ∣ m , Code-trans {succ x} {f n} {g m} c-sx≤fn c-fn≤gm ∣ })
                   (f-g-∥csim∥ n) }
  Code-trans {succ x} {limit f {f↑}} {bisim g {g↑} h {h↑} p i} c-x≤y =
    isProp→PathP {B = λ i → Code (limit f {f↑}) (bisim g {g↑} h {h↑} p i)
                          → Code (succ x) (bisim g {g↑} h {h↑} p i)}
                 (λ i → isProp→ (isPropCode (succ x) (bisim g {g↑} h {h↑} p i)))
                 (Code-trans {succ x} {limit f {f↑}} {limit g {g↑}} c-x≤y)
                 (Code-trans {succ x} {limit f {f↑}} {limit h {h↑}} c-x≤y)
                 i

  Code-trans {succ x} {limit f {f↑}} {trunc z₁ z₂ p q i j} c-x≤y =
    isProp→SquareP {B = λ i j → Code (limit f {f↑}) (trunc z₁ z₂ p q i j)
                              → Code (succ x) (trunc z₁ z₂ p q i j)}
                   (λ i j → isProp→ (isPropCode (succ x) (trunc z₁ z₂ p q i j)))
                   refl
                   refl
                   (λ j → Code-trans {succ x} {limit f {f↑}} {p j} c-x≤y)
                   (λ j → Code-trans {succ x} {limit f {f↑}} {q j} c-x≤y)
                   i j
  Code-trans {succ x} {bisim f {f↑} g {g↑} p i} {y} =
    isProp→PathP {B = λ i → Code (succ x) (bisim f {f↑} g {g↑} p i)
                          → Code (bisim f {f↑} g {g↑} p i) y → Code (succ x) y}
                 (λ i → isProp→ (isProp→ (isPropCode (succ x) y)))
                 (Code-trans {succ x} {limit f {f↑}} {y})
                 (Code-trans {succ x} {limit g {g↑}} {y}) i
  Code-trans {succ x} {trunc z₁ z₂ p q i j} {y} =
    isProp→SquareP {B = λ i j → Code (succ x) (trunc z₁ z₂ p q i j)
                              → Code (trunc z₁ z₂ p q i j) y → Code (succ x) y}
                   (λ i j → isProp→ (isProp→ (isPropCode (succ x) y)))
                   refl
                   refl
                   (λ j → Code-trans {succ x} {p j} {y})
                   (λ j → Code-trans {succ x} {q j} {y}) i j
  Code-trans {limit f} {succ y} {succ z} c-⊔f≤sy c-sy≤sz = λ k → Code-trans {f k} {succ y} {succ z}
                                                                            (c-⊔f≤sy k) c-sy≤sz
  Code-trans {limit f} {succ y} {limit h} c-⊔f≤sy c-sy≤hn k =
    ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (succ y) (h n)}
          {P = ∥ Σ[ n ∈ ℕ ] Code (f k) (h n) ∥}
          isPropPropTrunc
          (λ { (n , c-sy≤hn) → ∣ n , Code-trans {f k} {succ y} {h n} (c-⊔f≤sy k) c-sy≤hn ∣ })
          c-sy≤hn
  Code-trans {limit f {f↑}} {succ y} {bisim g {g↑} h {h↑} p i} c-x≤y =
    isProp→PathP {B = λ i → Code (succ y) (bisim g {g↑} h {h↑} p i)
                          → Code (limit f {f↑}) (bisim g {g↑} h {h↑} p i)}
                 (λ i → isProp→ (isPropCode (limit f {f↑}) (bisim g {g↑} h {h↑} p i)))
                 (Code-trans {limit f {f↑}} {succ y} {limit g {g↑}} c-x≤y)
                 (Code-trans {limit f {f↑}} {succ y} {limit h {h↑}} c-x≤y) i
  Code-trans {limit f {f↑}} {succ y} {trunc z₁ z₂ p q i j} c-x≤y =
    isProp→SquareP {B = λ i j → Code (succ y) (trunc z₁ z₂ p q i j)
                              → Code (limit f {f↑}) (trunc z₁ z₂ p q i j)}
                   (λ i j → isProp→ (isPropCode (limit f {f↑}) (trunc z₁ z₂ p q i j)))
                   refl
                   refl
                   (λ j → Code-trans {limit f {f↑}} {succ y} {p j} c-x≤y)
                   (λ j → Code-trans {limit f {f↑}} {succ y} {q j} c-x≤y) i j
  Code-trans {limit f} {limit g} {succ z} c-⊔f≤⊔g c-⊔g≤sz k =
    ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (f k) (g n)}
          {P = Code (f k) (succ z)}
          (isPropCode (f k) (succ z))
          (λ { (l , c-fk≤gn) → Code-trans {f k} {g l} {succ z} c-fk≤gn (c-⊔g≤sz l) })
          (c-⊔f≤⊔g k)
  Code-trans {limit f} {limit g} {limit h} c-f≤gn c-g≤hn k =
    ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (f k) (g n)}
          {P = ∥ Σ[ n ∈ ℕ ] Code (f k) (h n) ∥}
          isPropPropTrunc
          (λ { (l , c-fk≤gl) →
            ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (g l) (h n)}
                  {P = ∥ Σ[ n ∈ ℕ ] Code (f k) (h n) ∥}
                  isPropPropTrunc
                  (λ { (l' , c-gl≤hl') → ∣ l' , Code-trans {f k} {g l} {h l'} c-fk≤gl c-gl≤hl' ∣ })
                  (c-g≤hn l) })
          (c-f≤gn k)
  Code-trans {limit f {f↑}} {limit g {g↑}} {bisim h {h↑} k {k↑} p i} c-x≤y =
    isProp→PathP {B = λ i → Code (limit g {g↑}) (bisim h {h↑} k {k↑} p i)
                          → Code (limit f {f↑}) (bisim h {h↑} k {k↑} p i)}
                 (λ i → isProp→ (isPropCode (limit f {f↑}) (bisim h {h↑} k {k↑} p i)))
                 (Code-trans {limit f {f↑}} {limit g {g↑}} {limit h {h↑}} c-x≤y)
                 (Code-trans {limit f {f↑}} {limit g {g↑}} {limit k {k↑}} c-x≤y)
                 i
  Code-trans {limit f {f↑}} {limit g {g↑}} {trunc z₁ z₂ p q i j} c-x≤y =
    isProp→SquareP {B = λ i j → Code (limit g {g↑}) (trunc z₁ z₂ p q i j)
                              → Code (limit f {f↑}) (trunc z₁ z₂ p q i j)}
                   (λ i j → isProp→ (isPropCode (limit f {f↑}) (trunc z₁ z₂ p q i j)))
                   refl
                   refl
                   (λ j → Code-trans {limit f {f↑}} {limit g {g↑}} {p j} c-x≤y)
                   (λ j → Code-trans {limit f {f↑}} {limit g {g↑}} {q j} c-x≤y)
                   i j
  Code-trans {limit f {f↑}} {bisim g {g↑} h {h↑} p i} {y} =
    isProp→PathP {B = λ i → Code (limit f {f↑}) (bisim g {g↑} h {h↑} p i)
                          → Code (bisim g {g↑} h {h↑} p i) y → Code (limit f {f↑}) y}
                 (λ i → isProp→ (isProp→ (isPropCode (limit f {f↑}) y)))
                 (Code-trans {limit f {f↑}} {limit g {g↑}} {y})
                 (Code-trans {limit f {f↑}} {limit h {h↑}} {y}) i
  Code-trans {limit f {f↑}} {trunc z₁ z₂ p q i j} {y} =
    isProp→SquareP {B = λ i j → Code (limit f {f↑}) (trunc z₁ z₂ p q i j)
                              → Code (trunc z₁ z₂ p q i j) y → Code (limit f {f↑}) y}
                   (λ i j → isProp→ (isProp→ (isPropCode (limit f {f↑}) y)))
                   refl
                   refl
                   (λ j → Code-trans {limit f {f↑}} {p j} {y})
                   (λ j → Code-trans {limit f {f↑}} {q j} {y})
                   i j
  Code-trans {bisim f {f↑} g {g↑} p i} {x} {y} =
    isProp→PathP {B = λ i → Code (bisim f {f↑} g {g↑} p i) x
                          → Code x y → Code (bisim f {f↑} g {g↑} p i) y}
                 (λ i → isProp→ (isProp→ (isPropCode (bisim f {f↑} g {g↑} p i) y)))
                 (Code-trans {limit f {f↑}} {x} {y})
                 (Code-trans {limit g {g↑}} {x} {y}) i
  Code-trans {trunc z₁ z₂ p q i j} {x} {y} =
    isProp→SquareP {B = λ i j → Code (trunc z₁ z₂ p q i j) x
                              → Code x y → Code (trunc z₁ z₂ p q i j) y}
                   (λ i j → isProp→ (isProp→ (isPropCode (trunc z₁ z₂ p q i j) y)))
                   refl
                   refl
                   (λ j → Code-trans {p j} {x} {y})
                   (λ j → Code-trans {q j} {x} {y}) i j

  -- Reflexivity of Code
  Code-refl : ∀ {x} → Code x x
  Code-refl {zero} = tt
  Code-refl {succ x} = Code-refl {x}
  Code-refl {limit f} = λ k → ∣ (k , Code-refl {f k}) ∣
  Code-refl {bisim f {f↑} g {g↑} p i} =
    isProp→PathP (λ i → isPropCode (bisim f {f↑} g {g↑} p i) (bisim f {f↑} g {g↑} p i))
                 (λ k → ∣ (k , Code-refl {f k}) ∣)
                 (λ k → ∣ (k , Code-refl {g k}) ∣) i
  Code-refl {trunc x y p q i j} =
    isProp→SquareP {B = λ i j → Code (trunc x y p q i j) (trunc x y p q i j)}
                   (λ i j → isPropCode (trunc x y p q i j) (trunc x y p q i j))
                   (λ j → Code-refl {x})
                   (λ j → Code-refl {y})
                   (λ j → Code-refl {p j})
                   (λ j → Code-refl {q j})
                   i j

  -- An auxiliary lemma
  Code-cocone : ∀ (f : ℕ -> Brw) {f↑} k x → Code x (f k) -> Code x (limit f {f↑})
  Code-cocone f k zero p = tt
  Code-cocone f k (succ x) p = ∣ k , p ∣
  Code-cocone f k (limit g) p = λ l → ∣ (k , Code-trans {x = g l} (Code-cocone-simple g l) p) ∣
  -- With the simple case unfolded, we have this:
  -- Code-cocone f k (limit g) p =
  --   λ l → ∣ k , Code-trans {x = g l} (Code-cocone g l (g l) (Code-refl {g l})) p ∣
  Code-cocone f {f↑} k (bisim g {g↑} h {h↑} q i) =
    isProp→PathP {B = λ i → Code (bisim g h q i) (f k)
                          → Code (bisim g {g↑} h {h↑} q i) (limit f {f↑})}
                 (λ i → isProp→ (isPropCode (bisim g {g↑} h {h↑} q i) (limit f {f↑})))
                 (Code-cocone f {f↑} k (limit g {g↑}))
                 (Code-cocone f {f↑} k (limit h {h↑}))
                 i
  Code-cocone f {f↑} k (trunc x y p q i j) =
    isProp→SquareP {B = λ i j → Code (trunc x y p q i j) (f k)
                              → Code (trunc x y p q i j) (limit f {f↑})}
                   (λ i j → isProp→ (isPropCode (trunc x y p q i j) (limit f {f↑})))
                   refl
                   refl
                   (λ j → Code-cocone f {f↑} k (p j))
                   (λ j → Code-cocone f {f↑} k (q j))
                   i j

  Code-cocone-simple : ∀ (f : ℕ -> Brw) {f↑} k -> Code (f k) (limit f {f↑})
  Code-cocone-simple f {f↑} k = Code-cocone f {f↑} k (f k) (Code-refl {f k})

  Code-succ-incr-simple : ∀ {x} → Code x (succ x)
  Code-succ-incr-simple {zero} = tt
  Code-succ-incr-simple {succ x} = Code-succ-incr-simple {x}
  Code-succ-incr-simple {limit f {f↑}} = λ k → Code-trans {x = f k} {y = succ (f k)}
                                                          (Code-succ-incr-simple {f k})
                                                          (Code-cocone-simple f {f↑} k)
  Code-succ-incr-simple {bisim f {f↑} g {g↑} p i} =
    isProp→PathP {B = λ i → Code (bisim f {f↑} g {g↑} p i) (succ (bisim f g p i))}
                 (λ i → isPropCode (bisim f {f↑} g {g↑} p i) (succ (bisim f g p i)))
                 (Code-succ-incr-simple {limit f {f↑}})
                 (Code-succ-incr-simple {limit g {g↑}}) i
  Code-succ-incr-simple {trunc x y p q i j} =
    isProp→SquareP {B = λ i j → Code (trunc x y p q i j) (succ (trunc x y p q i j))}
                   (λ i j → isPropCode (trunc x y p q i j) (succ (trunc x y p q i j)))
                   refl
                   refl
                   (λ j → Code-succ-incr-simple {p j})
                   (λ j → Code-succ-incr-simple {q j})
                   i j

  {- We need to simultaneously define the difficult direction of the correctness of Code.

     This is marked as terminating for the following reason:
     From Code, we call ≤→Code with arguments unpacked by ∥-∥rec,
     which is not seen as structurally smaller by Agda. This is
     justified since this function goes into a Prop, which means that
     there is an equivalent induction principle with those arguments
     already unpacked. Implementing this workaround (to avoid the
     flag is work in progress.
  -}
  {-# TERMINATING #-}
  ≤→Code : ∀ {x y} → x ≤ y → Code x y
  ≤→Code {.zero} {y} ≤-zero = tt
  ≤→Code {x} {y} (≤-trans {x} {x₁} {y} x≤x₁ x₁≤y) =
    Code-trans {x} {x₁} {y} (≤→Code x≤x₁) (≤→Code x₁≤y)
  ≤→Code {.(succ x)} {.(succ y)} (≤-succ-mono {x} {y} x≤y) = ≤→Code x≤y
  ≤→Code {zero} {.(limit f)} (≤-cocone f {f↑} {k} x≤fk) = tt
  ≤→Code {succ x} {.(limit f)} (≤-cocone f {f↑} {k} x≤fk) = ∣ k , ≤→Code x≤fk ∣
  ≤→Code {limit g {g↑}} {.(limit f)} (≤-cocone f {f↑} {k} ⊔g≤fk)
    = λ l → ∣ (k , Code-trans {x = g l} (Code-cocone-simple g l) (≤→Code ⊔g≤fk)) ∣
  ≤→Code {bisim g {g↑} h {h↑} p i} {.(limit f)} (≤-cocone f {f↑} {k} x≤fk) =
    isProp→PathP {B = λ i → bisim g h p i ≤ limit f → Code (bisim g {g↑} h {h↑} p i) (limit f {f↑})}
                 (λ i → isProp→ (isPropCode (bisim g {g↑} h {h↑} p i) (limit f {f↑})))
                 (≤→Code {limit g {g↑}} {limit f {f↑}})
                 (≤→Code {limit h {h↑}} {limit f {f↑}})
                 i
                 (≤-cocone f {f↑} {k} x≤fk)
  ≤→Code {trunc x y p q i j} {.(limit f)} (≤-cocone f {f↑} {k} x≤fk) =
    isProp→SquareP {B = λ i j → trunc x y p q i j ≤ limit f
                              → Code (trunc x y p q i j) (limit f {f↑})}
                   (λ i j → isProp→ (isPropCode (trunc x y p q i j) (limit f {f↑})))
                   (λ j → ≤→Code {x} {limit f {f↑}})
                   (λ j → ≤→Code {y} {limit f {f↑}})
                   (λ j → ≤→Code {p j} {limit f {f↑}})
                   (λ j → ≤→Code {q j} {limit f {f↑}}) i j (≤-cocone f {f↑} {k} x≤fk)

  ≤→Code {.(limit f)} {zero} (≤-limiting f {f↑} f≤z) = lim≰zero {f} {f↑} (≤-limiting f f≤z)
  ≤→Code {.(limit f)} {succ y} (≤-limiting f f≤sy) k = ≤→Code {f k} {succ y} (f≤sy k)

  ≤→Code {.(limit f)} {limit g {g↑}} (≤-limiting f {f↑} f≤⊔g) k =
    ∥-∥rec {A = Σ ℕ (λ n → Code (succ (f k)) (g n))}
          {P =  ∥ Σ ℕ (λ n → Code (f k) (g n)) ∥}
          isPropPropTrunc
          (λ { (l , sfk≤gl) →
            ∣ l , Code-trans {x = f k} {y = succ (f k)} (Code-succ-incr-simple {f k}) sfk≤gl ∣ })
          (Code-trans {x = succ (f k)} {y = f (suc k)} (≤→Code (f↑ k)) (≤→Code (f≤⊔g (suc k))))

  ≤→Code {.(limit f)} {bisim g {g↑} h {h↑} p i} (≤-limiting f {f↑} f≤y) =
    isProp→PathP {B = λ i → limit f ≤ bisim g {g↑} h {h↑} p i
                          → Code (limit f {f↑}) (bisim g {g↑} h {h↑} p i)}
                 (λ i → isProp→ (isPropCode (limit f {f↑}) (bisim g {g↑} h {h↑} p i)))
                 (≤→Code {limit f {f↑}} {limit g {g↑}})
                 (≤→Code {limit f {f↑}} {limit h {h↑}}) i (≤-limiting f {f↑} f≤y)
  ≤→Code {.(limit f)} {trunc x y p q i j} (≤-limiting f {f↑} f≤y) =
    isProp→SquareP {B = λ i j → limit f ≤ trunc x y p q i j
                              → Code (limit f {f↑}) (trunc x y p q i j)}
                   (λ i j → isProp→ (isPropCode (limit f {f↑}) (trunc x y p q i j)))
                   (λ j → ≤→Code {limit f {f↑}} {x})
                   (λ j → ≤→Code {limit f {f↑}} {y})
                   (λ j → ≤→Code {limit f {f↑}} {p j})
                   (λ j → ≤→Code {limit f {f↑}} {q j}) i j (≤-limiting f {f↑} f≤y)

  ≤→Code {x} {y} (≤-trunc x≤y x≤y₁ i) = isPropCode x y (≤→Code x≤y) (≤→Code x≤y₁) i


{- End of the mutual definition.

Note: Above, we have defined:

≤→Code : (x ≤ y) → Code x y
Code-trans : Code x y → Code y z → C x z

In an older approach, we instead defined the following:

(x ≤ y) → Code y z → Code x z
Code x y → (y ≤ z) → Code x z

Interestingly, Code-trans is defined by triple-induction on ordinals,
while the others are defined by induction on ≤.
-}


{-
   ## Using Code, we can characterise the relation ≤.
   We have already defined ≤→Code in the big mutual definition;
   we now define the other direction, Code→≤.
   Together, they prove the correctness of Code.
-}

-- See the discussion above
{-# TERMINATING #-}
Code→≤ : ∀ {x y} → Code x y → x ≤ y

Code→≤ {zero} {y} c-x≤y = ≤-zero

Code→≤ {succ x} {succ y} c-sx≤sy = ≤-succ-mono (Code→≤ {x} {y} c-sx≤sy)
Code→≤ {succ x} {limit g {g↑}} =
  ∥-∥rec {A = Σ[ n ∈ ℕ ] Code (succ x) (g n)}
         {P = succ x ≤ limit g}
         ≤-trunc
         (λ {(n , c-sx≤gn) → ≤-trans (Code→≤ {succ x} {g n} c-sx≤gn) (≤-cocone-simple g) })
Code→≤ {succ x} {bisim g {g↑} h {h↑} g≈h i} =
  isProp→PathP {B = λ i → Code (succ x) (bisim g {g↑} h {h↑} g≈h i)
                        → succ x ≤ bisim g {g↑} h {h↑} g≈h i}
               (λ i → isProp→ ≤-trunc)
               (∥-∥rec ≤-trunc
                       λ {(n , c-sx≤gn) → ≤-trans (Code→≤ {succ x} {g n} c-sx≤gn)
                                                          (≤-cocone-simple g)})
               (∥-∥rec ≤-trunc
                       λ {(n , c-sx≤hn) → ≤-trans (Code→≤ {succ x} {h n} c-sx≤hn)
                                                          (≤-cocone-simple h)})
               i
Code→≤ {succ x} {trunc y₁ y₂ p q i j} =
  isProp→SquareP {B = λ i j → Code (succ x) (trunc y₁ y₂ p q i j) → succ x ≤ trunc y₁ y₂ p q i j}
                 (λ i j → isProp→ ≤-trunc)
                 (λ j → Code→≤ {succ x} {y₁})
                 (λ j → Code→≤ {succ x} {y₂})
                 (λ j → Code→≤ {succ x} {p j})
                 (λ j → Code→≤ {succ x} {q j})
                 i j

Code→≤ {limit f {f↑}} {succ y} c-⊔f≤sy = ≤-limiting f {f↑} {succ y} λ k → Code→≤ (c-⊔f≤sy k)
Code→≤ {limit f {f↑}} {limit g {g↑}} c-⊔f≤⊔g =
  ≤-limiting f {f↑} {limit g}
             (λ k → ∥-∥rec  ≤-trunc
                           (λ {(n , c-fk≤gn) → ≤-trans (Code→≤ c-fk≤gn) (≤-cocone-simple g) })
                           (c-⊔f≤⊔g k))

Code→≤ {limit f {f↑}} {bisim g {g↑} h {h↑} g≈h i} =
  isProp→PathP {B = λ i → Code (limit f {f↑}) (bisim g {g↑} h {h↑} g≈h i)
                        → limit f {f↑} ≤ bisim g {g↑} h {h↑} g≈h i}
               (λ i → isProp→ ≤-trunc)
               (λ c-⊔f≤⊔g → ≤-limiting f {f↑}
                                       (λ k → ∥-∥rec ≤-trunc
                                                    (λ {(n , c-fk≤gn) →
                                                      ≤-trans (Code→≤ c-fk≤gn)
                                                              (≤-cocone-simple g) })
                                                    (c-⊔f≤⊔g k)))
               (λ c-⊔f≤⊔h → ≤-limiting f {f↑}
                                       (λ k → ∥-∥rec ≤-trunc
                                                    (λ {(n , c-fk≤hn) →
                                                      ≤-trans (Code→≤ c-fk≤hn)
                                                              (≤-cocone-simple h) })
                                                    (c-⊔f≤⊔h k)))
               i
Code→≤ {limit f {f↑}} {trunc y₁ y₂ p q i j} =
  isProp→SquareP {B = λ i j → Code (limit f {f↑}) (trunc y₁ y₂ p q i j)
                            → limit f {f↑} ≤ trunc y₁ y₂ p q i j}
                 (λ i j → isProp→ ≤-trunc)
                 (λ j → Code→≤ {limit f {f↑}} {y₁})
                 (λ j → Code→≤ {limit f {f↑}} {y₂})
                 (λ j → Code→≤ {limit f {f↑}} {p j})
                 (λ j → Code→≤ {limit f {f↑}} {q j}) i j
Code→≤ {bisim f {f↑} g {g↑} p i} {y} =
  isProp→PathP {B = λ i → Code (bisim f {f↑} g {g↑} p i) y → bisim f {f↑} g {g↑} p i ≤ y}
               (λ i → isProp→ ≤-trunc)
               (Code→≤ {limit f {f↑}} {y})
               (Code→≤ {limit g {g↑}} {y}) i

Code→≤ {trunc x y p q i j} {z} =
  isProp→SquareP {B = λ i j → Code (trunc x y p q i j) z → trunc x y p q i j ≤ z}
                 (λ i j → isProp→ ≤-trunc)
                 (λ j → Code→≤ {x} {z})
                 (λ j → Code→≤ {y} {z})
                 (λ j → Code→≤ {p j} {z})
                 (λ j → Code→≤ {q j} {z}) i j
