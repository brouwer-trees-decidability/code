----------------------------------------------------------------------------------------------------
-- Decidability results for binary joins of Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Decidability.Joins where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Nat as N using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order as N using ()
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
  using (¬_; Dec; yes; no; isPropDec; mapDec; Dec→Stable)

open import PropTrunc

open import General-Properties
open import Iff

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Classifiability
open import BrouwerTree.Arithmetic
open import BrouwerTree.Code.Results
open import BrouwerTree.Decidability
open import BrouwerTree.Decidability.Finite


module with-ω where

  _⊔ω : Brw → Brw
  x ⊔ω with decIsFinite x
  ... | yes x-finite = ω
  ... | no x-infinite = x

  is-join : ∀ x → (x ⊔ω) is-join-of x and ω
  is-join x with decIsFinite x
  ... | yes x-finite = (∥-∥rec isProp⟨≤⟩ (λ { (n , ιn=x) → subst (_≤ ω) ιn=x (≤-cocone-simple ι)  }) (fst (isFinite-correct x) x-finite) , ≤-refl) , λ y p q → q
  ... | no x-infinite = (≤-refl , notFinite→ω≤ x x-infinite) , λ y p q → p

module with-finite where

  _⊔_ : Brw → ℕ → Brw
  x ⊔ zero = x
  zero ⊔ suc n = ι (suc n)
  succ x ⊔ suc n = succ (x ⊔ n)
  limit f {f↑} ⊔ suc n = limit f {f↑}
  bisim f {f↑} g {g↑} f∼g i ⊔ suc n = bisim f {f↑} g {g↑} f∼g i
  trunc x y p q i j ⊔ suc n = trunc (x ⊔ suc n) (y ⊔ suc n) (λ j → p j ⊔ suc n) (λ j → q j ⊔ suc n) i j

  is-join : ∀ x n → (x ⊔ n) is-join-of x and (ι n)
  is-join x zero = (≤-refl , ≤-zero) , (λ y x≤y _ → x≤y)
  is-join zero (suc n) = (≤-zero , ≤-refl) , (λ y _ p → p)
  is-join (succ x) (suc n) = ((≤-succ-mono (fst (fst (is-join x n)))) , ≤-succ-mono (snd (fst (is-join x n)))) , succCase
    where
      succCase : ∀ {n x} → (y : Brw) → succ x ≤ y → succ (ι n) ≤ y → succ (x ⊔ n) ≤ y
      succCase zero p q = ⊥.rec (succ≰zero p)
      succCase {n} {x} (succ y) p q = ≤-succ-mono (snd (is-join x n) y (≤-succ-mono⁻¹ p) (≤-succ-mono⁻¹ q))
      succCase {n} {x} (limit f {f↑}) p q =
        ∥-∥rec isProp⟨<⟩ (λ { (m , x<fm) → ∥-∥rec isProp⟨<⟩ (λ { (k , ιn<fk) →
           ≤∘<-in-< (snd (is-join x n) (f (N.max m k)) (<-in-≤ (<∘≤-in-< x<fm (increasing-monotone f↑ N.left-≤-max)))
                                                     (<-in-≤ (<∘≤-in-< ιn<fk (increasing-monotone f↑ (N.right-≤-max {m = m}))))) (<-cocone-simple f) })
                                    (below-limit-lemma _ f q)  })
                        (below-limit-lemma x f p)
      succCase {n} {x} (bisim f {f↑} g {g↑} f~g i) p q = isProp→PathP {B = λ i → (p : succ x ≤ bisim f g f~g i) → (q : succ (ι n) ≤ bisim f g f~g i) → succ (x ⊔ n) ≤ bisim f g f~g i} (λ i → isProp→ (isProp→ isProp⟨≤⟩)) (λ p q → ∥-∥rec isProp⟨<⟩ (λ { (m , x<fm) → ∥-∥rec isProp⟨<⟩ (λ { (k , ιn<fk) → ≤∘<-in-< (snd (is-join x n) (f (N.max m k)) (<-in-≤ (<∘≤-in-< x<fm (increasing-monotone f↑ N.left-≤-max))) (<-in-≤ (<∘≤-in-< ιn<fk (increasing-monotone f↑ (N.right-≤-max {m = m}))))) (<-cocone-simple f) }) (below-limit-lemma _ f q)  }) (below-limit-lemma x f p)) (λ p q → ∥-∥rec isProp⟨<⟩ (λ { (m , x<gm) → ∥-∥rec isProp⟨<⟩ (λ { (k , ιn<gk) → ≤∘<-in-< (snd (is-join x n) (g (N.max m k)) (<-in-≤ (<∘≤-in-< x<gm (increasing-monotone g↑ N.left-≤-max))) (<-in-≤ (<∘≤-in-< ιn<gk (increasing-monotone g↑ (N.right-≤-max {m = m}))))) (<-cocone-simple g) }) (below-limit-lemma _ g q)  }) (below-limit-lemma x g p)) i p q
      succCase {n} {z} (trunc x y p q i j) r w = isProp→SquareP' {B = λ i j → (r : succ z ≤ trunc x y p q i j) → (w : succ (ι n) ≤ trunc x y p q i j) → succ (z ⊔ n) ≤ trunc x y p q i j} (λ i j → isProp→ (isProp→ isProp⟨≤⟩)) (λ j r w → succCase x r w) (λ j r w → succCase y r w) (λ j r w → succCase (p j) r w) (λ j r w → succCase (q j) r w) i j r w
  is-join (limit f) (suc n) = (≤-refl , ι n <lim) , λ y p q → p
  is-join (bisim f g x i) (suc n) = isProp→PathP {B = λ i → bisim f g x i is-join-of bisim f g x i and succ (ι n)} (λ i → isProp⟨is-join-of⟩ isProp⟨≤⟩) ((≤-refl , ι n <lim) , λ y p q → p) ((≤-refl , ι n <lim) , λ y p q → p) i
  is-join (trunc x y p q i j) (suc n) = isProp→SquareP' {B = λ i j → (trunc x y p q i j ⊔ suc n) is-join-of trunc x y p q i j and ι (suc n)} (λ i j → isProp⟨is-join-of⟩ isProp⟨≤⟩)
                                          (λ j → is-join x (suc n))
                                          (λ j → is-join y (suc n))
                                          (λ j → is-join (p j) (suc n))
                                          ((λ j → is-join (q j) (suc n))) i j

  -- additional properties (not needed above)

  zero⊔n≡n : ∀ n → zero ⊔ n ≡ ι n
  zero⊔n≡n zero = refl
  zero⊔n≡n (suc n) = refl

  ⊔-mono-right : ∀ x n m → ι n ≤ ι m → (x ⊔ n) ≤ (x ⊔ m)
  ⊔-mono-right x zero zero _ = ≤-refl
  ⊔-mono-right zero zero (suc m) p = p
  ⊔-mono-right (succ x) zero (suc m) _
    = ≤-succ-mono (⊔-mono-right x zero m ≤-zero)
  ⊔-mono-right (limit f) zero (suc m) p = ≤-refl
  ⊔-mono-right (bisim f g x i) zero (suc m) p = ≤-refl
  ⊔-mono-right (trunc x y p q i j) zero (suc m) r =
    isProp→SquareP' {B = λ i j → (trunc x y p q i j) ≤ trunc (x ⊔ suc m) (y ⊔ suc m) (λ j₁ → p j₁ ⊔ suc m) (λ j₁ → q j₁ ⊔ suc m) i j }
      (λ i j → ≤-trunc)
      (λ j → ⊔-mono-right x zero (suc m) r)
      ((λ j → ⊔-mono-right y zero (suc m) r))
      ((λ j → ⊔-mono-right (p j) zero (suc m) r))
      ((λ j → ⊔-mono-right (q j) zero (suc m) r)) i j
  ⊔-mono-right x (suc n) zero p = ⊥.rec (succ≰zero p)
  ⊔-mono-right zero (suc n) (suc m) p = p
  ⊔-mono-right (succ x) (suc n) (suc m) p
    = ≤-succ-mono (⊔-mono-right x n m (≤-succ-mono⁻¹ p))
  ⊔-mono-right (limit f) (suc n) (suc m) p = ≤-refl
  ⊔-mono-right (bisim f g x i) (suc n) (suc m) p = ≤-refl
  ⊔-mono-right (trunc x y p q i j) (suc n) (suc m) r =
    isProp→SquareP' {B = λ i j → (trunc (x ⊔ suc n) (y ⊔ suc n) (λ j₁ → p j₁ ⊔ suc n) (λ j₁ → q j₁ ⊔ suc n) i j) ≤ trunc (x ⊔ suc m) (y ⊔ suc m) (λ j₁ → p j₁ ⊔ suc m) (λ j₁ → q j₁ ⊔ suc m) i j }
      (λ i j → ≤-trunc)
      (λ j → ⊔-mono-right x (suc n) (suc m) r)
      ((λ j → ⊔-mono-right y (suc n) (suc m) r))
      ((λ j → ⊔-mono-right (p j) (suc n) (suc m) r))
      ((λ j → ⊔-mono-right (q j) (suc n) (suc m) r)) i j


module with-ω+1 where

  ⊔ω+1 : LPO → Brw → Brw
  ⊔ω+1 lpo x with Dec≤→Dec< (LPO→Dec≤ lpo) ω x
  ... | yes ω<x = x
  ... | no ¬ω<x = succ ω

  LPO→⊔ω+1 : (lpo : LPO) → (x : Brw) → (⊔ω+1 lpo x) is-join-of x and (succ ω)
  LPO→⊔ω+1 lpo x with Dec≤→Dec< (LPO→Dec≤ lpo) ω x
  ... | yes ω<x = (≤-refl , ω<x) , (λ y p q → p)
  ... | no ¬ω<x = (lemma x ¬ω<x , ≤-refl) , λ y p q → q where
    succ-finite : (x : Brw) → ¬ (ω < succ x) → isFinite x
    succ-finite = Brw-ind (λ x → ¬ (ω < succ x) → isFinite x) (λ x → isProp→ (isProp⟨isFinite⟩ x))
                          (λ _ → tt)
                          (λ {x} ih p → ih (λ q → p (<-trans _ _ _ q <-succ-incr-simple)))
                          λ {f} ih p → ⊥.rec (p (≤-succ-mono (ω-smallest f)))

    lemma : (x : Brw) → ¬ (ω < x) → x ≤ succ ω
    lemma = Brw-ind (λ x → ¬ (ω < x) → x ≤ succ ω) (λ x → isProp→ isProp⟨≤⟩)
                    (λ _ → ≤-zero)
                    (λ {x} ih p → ∥-∥rec isProp⟨≤⟩ (λ { (n , ιn=x) → subst (_< succ ω) ιn=x (≤-succ-mono (≤-cocone-simple ι)) }) (fst (isFinite-correct x) (succ-finite x p)))
                    λ {f} ih p → ≤-limiting f (λ k → ih k (λ q → p ((<-trans _ _ _ q (<-cocone-simple f)))))


  ⊔ω+1→Dec≡ω : (⊔ω+1 : Brw → Brw) → ((x : Brw) → (⊔ω+1 x) is-join-of x and (succ ω)) → (y : Brw) → Dec (y ≡ ω)
  ⊔ω+1→Dec≡ω ⊔ω+1 is-join = Brw-ind (λ y → Dec (y ≡ ω)) (λ x → isPropDec (Brw-is-set _ _))
                                    (no zero≠lim)
                                    (λ {x} _ → no succ≠lim)
                                    λ {f} {f↑} ih → limitCase f f↑ where
   limitCase : ∀ f f↑ → Dec (limit f {f↑} ≡ ω)
   limitCase f f↑ with Brw-has-classification (⊔ω+1 (limit f {f↑})) | is-join ((limit f {f↑}))
   ... | inl is-zero | ((p , _) , _) = ⊥.rec (lim≰zero (≤-trans p (is-zero zero)))
   ... | inr (inl (x , ((x<lf⊔ω+1 , p) , q))) | ((jl , jr) , ju)
     = yes (≤-antisym (≤-limiting f λ k → <-in-≤ (Dec→Stable (mapDec (λ p → ∥-∥rec isProp⟨≤⟩ (λ { (n , ιn≡fk) → subst (_< ω) ιn≡fk (<-cocone-simple ι) }) (fst (isFinite-correct (f k)) p))
                                                                     (λ p q → <-irreflexive _ (≤∘<-in-< (notFinite→ω≤ (f k) p) q))
                                                                     (decIsFinite (f k)))
                                                            λ ¬fk<ω → succ≠lim (sym lf⊔ω+1≡sx ∙ ≤-antisym (ju (limit f) ≤-refl (<-in-≤ (lf-greatest k (notFinite→ω≤ (f k) λ fin → ∥-∥rec isProp⊥ (λ { (n , ιn≡fk) → ¬fk<ω (subst (_< ω) ιn≡fk (<-cocone-simple ι)) }) (fst (isFinite-correct (f k)) fin))))) jl)))
                      (ω-smallest f))
     where
       lf⊔ω+1≡sx : ⊔ω+1 (limit f {f↑}) ≡ succ x
       lf⊔ω+1≡sx = ≤-antisym (p (succ x) ≤-refl) x<lf⊔ω+1
       lf-greatest : (k : ℕ) → ω ≤ f k → succ ω < limit f {f↑}
       lf-greatest k p = ≤-cocone f {k = suc (suc (suc k))} (≤-trans (≤-succ-mono (≤-succ-mono p)) (≤∘<-in-< (<-trans _ _ _ (f↑ k) (f↑ (suc k))) (f↑ (suc (suc k)))))

   ... | inr (inr is-lim) | _
     = ∥-∥rec (isPropDec (Brw-is-set _ _))
             (λ { ((g , g↑) , (cone , lim)) → no λ lg≡ω → ⊥.rec (succ≠lim {f↑ = g↑}
                                                                          (sym ( ≤-antisym (≤-limiting g cone) (lim (limit g) λ k → ≤-cocone-simple g) ∙ cong ⊔ω+1 lg≡ω ∙ ω⊔ω+1≡ω+1))) }) is-lim
     where
       ω⊔ω+1≡ω+1 : ⊔ω+1 ω ≡ succ ω
       ω⊔ω+1≡ω+1 = ≤-antisym (snd (is-join ω) (succ ω) ≤-succ-incr-simple ≤-refl) (snd (fst (is-join ω)))
