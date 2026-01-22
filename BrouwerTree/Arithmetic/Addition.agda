{-# OPTIONS --erased-cubical --erasure --guardedness  #-}

module BrouwerTree.Arithmetic.Addition where

open import Cubical.Data.Sigma

open import PropTrunc

open import BrouwerTree.Base
open import BrouwerTree.Properties

infixr 35 _+_

mutual
  _+_ : Brw → Brw → Brw
  x + zero = x
  x + (succ y) = succ (x + y)
  x + (limit f {f↑}) = limit (λ n → x + f n) {λ k → x+-mono (f↑ k)}
  x + (bisim f {f↑} g {g↑} (f≲g , g≲f) i) = bisim (λ n → x + f n)
                                                  {x+-preserves-increasing f↑}
                                                  (λ n → x + g n)
                                                  {x+-preserves-increasing g↑}
                                                  (x+-preserves-≲ f≲g , x+-preserves-≲ g≲f)
                                                  i
  x + (trunc y z p q i j) = trunc (x + y) (x + z) (λ j → x + (p j)) (λ j → x + (q j)) i j

  x+-mono : {x y z : Brw} → y ≤ z → x + y ≤ x + z
  x+-mono {z = z} ≤-zero = x+-increasing z
  x+-mono (≤-trans y≤z z≤w) = ≤-trans (x+-mono y≤z) (x+-mono z≤w)
  x+-mono (≤-succ-mono y≤z) = ≤-succ-mono (x+-mono y≤z)
  x+-mono (≤-cocone f {k = k} y≤fk) = ≤-cocone _ {k = k} (x+-mono y≤fk)
  x+-mono (≤-limiting f fk≤z) = ≤-limiting _ λ k → x+-mono (fk≤z k)
  x+-mono (≤-trunc p q i) = ≤-trunc (x+-mono p) (x+-mono q) i

  -- Agda does not see that the recursive call on `fk≤gl` is structurally smaller,
  -- because it has been uncovered under the propositional truncation. In the
  -- "official" induction principle, we instead get a family of truncated inductive hypothesis,
  -- and here we can uncover the k-th one because we are proving a proposition.
  -- To work around this, we mark the definition as terminating.
  {-# TERMINATING #-}
  x+-preserves-≲ : ∀ {x f g} → f ≲ g → (λ n → x + f n) ≲ (λ n → x + g n)
  x+-preserves-≲ f≲g k = ∥-∥rec isPropPropTrunc (λ (l , fk≤gl) → ∣ l , x+-mono fk≤gl ∣) (f≲g k)

  x+-increasing : ∀ {x} (z : Brw) → x ≤ x + z
  x+-increasing {x} zero = ≤-refl
  x+-increasing {x} (succ z) = ≤-succ-incr (x+-increasing z)
  x+-increasing {x} (limit f) = ≤-cocone _ {k = 5} (x+-increasing (f 5))
  x+-increasing {x} (bisim f {f↑} g {g↑} (f≲g , g≲f) i) =
      isProp→PathP' {B = λ i → x ≤ bisim _ _ (x+-preserves-≲ f≲g , x+-preserves-≲ g≲f) i}
                   (λ i → ≤-trunc)
                   (≤-cocone _ (x+-increasing (f 5)))
                   (≤-cocone _ (x+-increasing (g 5)))
                   i
  x+-increasing {x} (trunc y z p q i j) =
      isProp→SquareP' {B = λ i j → x ≤ trunc (x + y) (x + z) (λ j → x + p j) (λ j → x + q j) i j}
                     (λ i j → ≤-trunc)
                     (λ j → x+-increasing y)
                     (λ j → x+-increasing z)
                     (λ j → x+-increasing (p j))
                     (λ j → x+-increasing (q j))
                     i j

  x+-preserves-increasing : ∀ {x f} → increasing f → increasing (λ n → x + f n)
  x+-preserves-increasing f↑ k = x+-mono (f↑ k)

+x-mono : ∀ {x y} (z  : Brw) → x ≤ y → x + z ≤ y + z
+x-mono {x} {y} =
  Brw-ind (λ z → x ≤ y → x + z ≤ y + z)
          (λ z f g → λ i x → ≤-trunc (f x) (g x) i)
          (λ p → p)
          (λ ih p → ≤-succ-mono (ih p))
          (λ {f} {f↑} ih p → ≤-limiting _ λ k → ≤-cocone _ (ih k p))
