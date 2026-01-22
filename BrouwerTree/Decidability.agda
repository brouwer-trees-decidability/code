----------------------------------------------------------------------------------------------------
-- Decidability results for Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --guardedness --erasure #-}

module BrouwerTree.Decidability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as N
  using (ℕ ; zero ; suc; snotz; injSuc; +-zero; +-suc; m+n≡0→m≡0×n≡0)
open import Cubical.Data.Nat.Order as N
  using (≤-suc; ≤0→≡0; Trichotomy; zero-≤); open Trichotomy
open import Cubical.Relation.Nullary
  using (¬_; Dec; yes; no; Stable; mapDec; Dec→Stable; isPropDec)

open import PropTrunc

open import General-Properties

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Arithmetic
open import BrouwerTree.Arithmetic.Properties
open import BrouwerTree.Arithmetic.Correctness
open import BrouwerTree.Code.Results
open import BrouwerTree.Decidability.Finite

boundedDecidable : (P : ℕ → Type) → (∀ n → Dec (P n)) → (n : ℕ) → Σ ℕ P ⊎ ((m : ℕ) → m N.≤ n → ¬ (P m))
boundedDecidable P decP zero with decP zero
... | yes p = inl (zero , p)
... | no ¬p = inr λ m m≤0 → subst (λ z → P z → ⊥) (sym (≤0→≡0 m≤0)) ¬p
boundedDecidable P decP (suc n) with boundedDecidable P decP n
... | inl (m , pm) = inl (m , pm)
... | inr ¬p≤n with decP (suc n)
... | yes p = inl (suc n , p)
... | no ¬p[sucn] = inr f where
  f : (m : ℕ) → m N.≤ suc n → ¬ (P m)
  f m (zero , q) = subst (λ z → ¬ (P z)) (sym q) ¬p[sucn]
  f m (suc r , q) = ¬p≤n m (r , injSuc q)

some-below : (ℕ → Bool) → ℕ → Bool
some-below f zero = f zero
some-below f (suc n) = f (suc n) or some-below f n

all-false : {f : ℕ → Bool} → (n : ℕ) → ((k : ℕ) → k N.≤ n → f k ≡ false) → some-below f n ≡ false
all-false {f} zero fk≡false = fk≡false zero N.≤-refl
all-false {f} (suc n) fk≡false =
  cong₂ _or_ (fk≡false (suc n) N.≤-refl) (all-false {f} n λ k k≤n → fk≡false k (≤-suc k≤n))


indicator : (ℕ → Bool) → ℕ → Brw
indicator f n = if (some-below f n) then one else zero

indicator-≤one : {f : ℕ → Bool} → (n : ℕ) → indicator f n ≤ one
indicator-≤one {f} n with some-below f n
... | true = ≤-refl
... | false = ≤-zero

jumpSeq : (ℕ → Bool) → ℕ → Brw
jumpSeq f n = (ω · indicator f n) + ι n

jumpSeq-increasing : (f : ℕ → Bool) → increasing (jumpSeq f)
jumpSeq-increasing f k with some-below f k | f (suc k)
... | false | false = ≤-refl
... | false | true = ≤-succ-mono (+x-mono (ι k) ≤-zero)
... | true | false = ≤-refl
... | true | true = ≤-refl

limit[_]↑ : (ℕ → Bool) → Brw
limit[ s ]↑ = limit (jumpSeq s) {jumpSeq-increasing s}

ω·2 : Brw
ω·2 = ω + ω

jumpSeq≤ω2 : (f : ℕ → Bool) → limit (jumpSeq f) {jumpSeq-increasing f} ≤ ω·2
jumpSeq≤ω2 f = pointwise≤→≤ λ k → +-mono {x = ω · indicator f k} {ι k} {ω} {ι k}
                                         (≤-trans (x·-mono (indicator-≤one k)) (≤-refl-≡ (y·one≡y ω)) ) ≤-refl

ω<jumpSeq⟨n⟩→fm≡true : (f : ℕ → Bool) → (n : ℕ) → ω < jumpSeq f n → Σ[ m ∈ ℕ ] (f m ≡ true)
ω<jumpSeq⟨n⟩→fm≡true f n p with boundedDecidable (λ n → f n ≡ true) (λ n → f n ≟ true) n
... | inl (m , p) = (m , p)
... | inr x = ⊥.rec (<-irreflexive ω (<-trans _ _ _ p (absurd-otherwise λ m p → ¬true→false (f m) (x m p)))) where
  absurd-otherwise : ((m : ℕ) → m N.≤ n → f m ≡ false) → (jumpSeq f) n < ω
  absurd-otherwise fm=false = subst (λ z → (ω · (if z then one else zero)) + ι n < ω)
                                    (sym (all-false {f} n fm=false))
                                    (≤∘<-in-< (≤-refl-≡ (zero+y≡y (ι n))) (<-cocone-simple ι {ι-increasing} {n}))

jumpSeq-translate-back : (f : ℕ → Bool) → limit (jumpSeq f) ≡ ω + ω → Σ[ n ∈ ℕ ] (f n ≡ true)
jumpSeq-translate-back f p = least-witness (λ n → f n ≡ true) (λ n → isSetBool (f n) true) (λ n → f n ≟ true)
                                           (∥-∥rec isPropPropTrunc (λ (n , p) → ∣ ω<jumpSeq⟨n⟩→fm≡true f n p ∣)
                                           (below-limit-lemma ω (jumpSeq f) {jumpSeq-increasing f} (subst (λ z → ω < z) (sym p) ω<ω+ω)))

jumpSeq>ω-translate-back : (f : ℕ → Bool)
  → ω < limit (jumpSeq f) {jumpSeq-increasing f} → Σ[ n ∈ ℕ ] (f n ≡ true)
jumpSeq>ω-translate-back f p = least-witness (λ n → f n ≡ true) (λ n → isSetBool (f n) true) (λ n → f n ≟ true)
                                             (∥-∥rec isPropPropTrunc (λ (n , p) → ∣ ω<jumpSeq⟨n⟩→fm≡true f n p ∣)
                                                     (below-limit-lemma ω (jumpSeq f) p))

eventually-true : {f : ℕ → Bool} → (n : ℕ) → (f n ≡ true) → (k : ℕ) → n N.≤ k → some-below f k ≡ true
eventually-true {f} n fn≡true zero (zero , n=0) = sym (cong f n=0) ∙ fn≡true
eventually-true {f} n fn≡true zero (suc r , suc=0) = ⊥.rec (snotz suc=0)
eventually-true {f} n fn≡true (suc k) (zero , p) =
  subst (λ z → z or some-below f k ≡ true) (sym fn≡true ∙ cong f p) (or-zeroˡ (some-below f k))
eventually-true {f} n fn≡true (suc k) (suc r , p) =
  subst (λ z → f (suc k) or z ≡ true) (sym (eventually-true {f} n fn≡true k (r , injSuc p))) (or-zeroʳ (f (suc k)))


jumpSeq-translate-forth : (f : ℕ → Bool) → ∥ Σ[ n ∈ ℕ ] (f n ≡ true) ∥ → limit (jumpSeq f) {jumpSeq-increasing f} ≡ ω + ω
jumpSeq-translate-forth f = ∥-∥rec (Brw-is-set _ _) λ (n , p) → bisim _ _ (left , right n p) where
  left : (λ z → ω · indicator f z + ι z) ≲ (λ z → ω + ι z)
  left k with some-below f k
  ... | false = ∣ k , +x-mono (ι k) ≤-zero ∣
  ... | true = ∣ k , +x-mono (ι k) (subst (λ z → z  ≤ ω)
                                          (limit-pointwise-equal _ _ λ n → sym (zero+y≡y (ι n))) ≤-refl) ∣

  right : ∀ n p → (λ z → ω + ι z) ≲ (λ z → ω · indicator f z + ι z)
  right n p k = ∣ (n N.+ k) , +-mono (subst (λ z → z ≤ (ω · indicator f (n N.+ k))) (y·one≡y ω)
                                        (x·-mono (subst (λ z → succ zero ≤ (if z then succ zero else zero))
                                                        (sym (eventually-true n p (n N.+ k) (subst (λ z → z N.≤ n N.+ k)
                                                                                                     (+-zero n) (N.≤-k+ zero-≤))))
                                                        ≤-refl)))
                                 (ι-mono (N.≤-+k {0} {n} {k} zero-≤)) ∣

lim⟨jumpSeq⟩>ω→lim⟨jumpSeq⟩≡ω+ω : (s : ℕ → Bool)
  → ω < limit (jumpSeq s) {jumpSeq-increasing s}
  → limit (jumpSeq s) {jumpSeq-increasing s} ≡ ω + ω
lim⟨jumpSeq⟩>ω→lim⟨jumpSeq⟩≡ω+ω  s ls↑>ω = jumpSeq-translate-forth s ((∥-∥rec isPropPropTrunc (λ { (n , ω<s↑n) → ∣ ω<jumpSeq⟨n⟩→fm≡true s n ω<s↑n ∣ })
                                                                             (below-limit-lemma ω (jumpSeq s) {jumpSeq-increasing s} ls↑>ω)))

lim⟨jumpSeq⟩≡ω+ω→lim⟨jumpSeq⟩>ω : (s : ℕ → Bool)
  → limit (jumpSeq s) {jumpSeq-increasing s} ≡ ω + ω
  → ω < limit (jumpSeq s) {jumpSeq-increasing s}
lim⟨jumpSeq⟩≡ω+ω→lim⟨jumpSeq⟩>ω s e = subst (ω <_) (sym e) ω<ω+ω

lim⟨jumpSeq⟩<ω2→sk≡false : (s : ℕ → Bool) →
                           limit (jumpSeq s) < (ω + ω) → (k : ℕ) → s k ≡ false
lim⟨jumpSeq⟩<ω2→sk≡false s p k =
  Dec→Stable (s k ≟ false) (λ sk≠f → <-irreflexive-≡ (jumpSeq-translate-forth s ∣ (_ , ¬false→true _ sk≠f) ∣) p)


¬¬-functor : {ℓ ℓ' : Level}{A : Type ℓ}{B : Type ℓ'} → (A → B) → ¬ ¬ A → ¬ ¬ B
¬¬-functor f = λ z z₁ → z (λ z₂ → z₁ (f z₂))

equality-notnot-stable-taboo : ((x y : Brw) → Stable (x ≡ y)) → MP
equality-notnot-stable-taboo p f ¬¬∃nf[n]≡1 = jumpSeq-translate-back f (p (limit (jumpSeq f) {jumpSeq-increasing f}) (ω + ω)
                                                                     (¬¬-functor (λ x → jumpSeq-translate-forth f ∣ x ∣) ¬¬∃nf[n]≡1))

stable≡ω·2→MP : ((x : Brw) → Stable (x ≡ ω + ω)) → MP
stable≡ω·2→MP p f ¬¬∃nf[n]≡1 = jumpSeq-translate-back f (p (limit (jumpSeq f) {jumpSeq-increasing f})
                                                           (¬¬-functor (λ x → jumpSeq-translate-forth f ∣ x ∣) ¬¬∃nf[n]≡1))

Stable≡a+y→Stable≡y : ∀ a y → (∀ x → Stable (x ≡ a + y)) → (∀ x → Stable (x ≡ y))
Stable≡a+y→Stable≡y a y st x ¬¬x≡y = +-leftCancel a (st (a + x) (¬¬-functor (cong (a +_)) ¬¬x≡y))

stable≡ω·⟨n+2⟩→MP : ∀ n → 2 N.≤ n → (∀ x → Stable (x ≡ ω · ι n)) → MP
stable≡ω·⟨n+2⟩→MP zero 2≤0 st = ⊥.rec (N.¬-<-zero 2≤0)
stable≡ω·⟨n+2⟩→MP (suc zero) 2≤1 st = ⊥.rec (N.¬-<-zero (N.pred-≤-pred 2≤1))
stable≡ω·⟨n+2⟩→MP (suc (suc zero)) 2≤n st = stable≡ω·2→MP  (subst (λ z → ∀ x → Stable (x ≡ z)) (x·2=x+x ω) st)
stable≡ω·⟨n+2⟩→MP (suc (suc (suc n))) (zero , p) st = ⊥.rec (snotz (sym (injSuc (injSuc p))))
stable≡ω·⟨n+2⟩→MP (suc (suc (suc n))) (suc k , p) st = stable≡ω·⟨n+2⟩→MP (suc (suc n)) (k , injSuc p) (step n st)
  where
   step : ∀ n → (∀ x → Stable (x ≡ ω · ι (suc (suc (suc n))))) → (∀ x → Stable (x ≡ ω · ι (suc (suc n))))
   step n st = Stable≡a+y→Stable≡y ω (ω · (ι (suc (suc n)))) (subst (λ z → (x : Brw) → Stable (x ≡ z)) (x·n=1=x+xn {suc (suc n)} ω) st)

stable≡ω : (x : Brw) → Stable (x ≡ ω)
stable≡ω = Brw-ind (λ x → Stable (x ≡ ω))
                   (λ _ → isPropΠ λ _ → Brw-is-set _ _)
                   (λ ¬¬zero≡ω → ⊥.rec (¬¬zero≡ω zero≠lim))
                   (λ _ ¬¬succ≡ω → ⊥.rec (¬¬succ≡ω succ≠lim))
                   limit-case
 where
  limit-case : ∀ {f f↑} → (∀ i → Stable (f i ≡ ω)) → Stable (limit f {f↑} ≡ ω)
  limit-case {f} {f↑} _ ¬¬lim≡ω = ≤-antisym lim≤ω ω≤lim
   where
    f<ω : ∀ i → f i < ω
    f<ω i with <ω-or-≥ω (f i)
    ... | inl fi<ω = fi<ω
    ... | inr fi≥ω = ⊥.rec (¬¬lim≡ω (λ lim≡ω → <-irreflexive-≡ (sym lim≡ω) (≤∘<-in-< fi≥ω (<-cocone-simple f))))
    lim≤ω : limit f {f↑} ≤ ω
    lim≤ω = ≤-limiting f (<-in-≤ ∘ f<ω)
    ω≤lim : ω ≤ limit f {f↑}
    ω≤lim = ω-smallest f

equality-decidable-taboo : ((x y : Brw) → Dec (x ≡ y)) → MP
equality-decidable-taboo dec = equality-notnot-stable-taboo λ x y → Dec→Stable (dec x y)

splitting-≤ : Type
splitting-≤ = Splits Brw _<_ _≤_

splitting-≤-taboo : splitting-≤ → Σ-LPO
splitting-≤-taboo split f with split {limit (jumpSeq f) {jumpSeq-increasing f}} {ω + ω} (jumpSeq≤ω2 f)
... | inl jumpSeq<ω2 = inl λ k → ¬true→false (f k) λ fk≡true → <-irreflexive-≡ (jumpSeq-translate-forth f ∣ (k , fk≡true) ∣) jumpSeq<ω2
... | inr jumpSeq=ω2 = inr (jumpSeq-translate-back f jumpSeq=ω2)

BrwHasSubtraction : Type
BrwHasSubtraction = (x y : Brw) → x ≤ y → Σ[ y-x ∈ Brw ] x + y-x ≡ y

has-sub-to-BrwHasSubtraction : has-sub → BrwHasSubtraction
has-sub-to-BrwHasSubtraction (f , p) x y x≤y = f y x x≤y , p y x x≤y

BrwHasSubtraction-to-has-sub : BrwHasSubtraction → has-sub
BrwHasSubtraction-to-has-sub sub = (λ y x x≤y → fst (sub x y x≤y)) , (λ y x x≤y → snd (sub x y x≤y))

Brw-sub-is-unique : has-sub → has-unique-sub
Brw-sub-is-unique (sub , is) =
  ((sub , is)) , (λ { (sub' , is') → Σ≡Prop (isProp⟨is-sub⟩ Brw-is-set)
                                          (funExt λ x → funExt λ y → funExt λ p → +-leftCancel y (is x y p ∙ sym (is' x y p))) })

BrwHasSubtraction-to-splitting-≤ : BrwHasSubtraction → splitting-≤
BrwHasSubtraction-to-splitting-≤ sub {x} {y} x≤y with sub x y x≤y
BrwHasSubtraction-to-splitting-≤ sub {x} {y} x≤y | (y-x , x+y-x≡y) with decZero y-x
... | yes y-x≡0 = inr (subst (λ z → x + z ≡ y) y-x≡0 x+y-x≡y)
... | no  y-x≠0 = inl (<∘≤-in-< (x+-mono-< (zero≠x→zero<x y-x λ p → y-x≠0 (sym p))) (≤-refl-≡ x+y-x≡y))


Dec≡a+y→Dec≡y : ∀ a y → (∀ x → Dec (x ≡ a + y)) → (∀ x → Dec (x ≡ y))
Dec≡a+y→Dec≡y a y d x = mapDec (+-leftCancel a) (λ p q → p (cong (a +_) q)) (d (a + x))

limit-drop-initial : ∀ n f {f↑} → limit f {f↑} ≡ limit (λ k → f (k N.+ n)) {λ k → f↑ (k N.+ n)}
limit-drop-initial n f {f↑} = bisim _ _ ((λ k → ∣ k , increasing→monotone f↑ (subst (λ z → z N.≤ k N.+ n) (+-zero k) (N.≤-k+ {k = k} zero-≤)) ∣) , λ k → ∣ k N.+ n , ≤-refl ∣)


isProp⟨BrwHasSubtraction⟩ : ∀ {x y} → isProp (Σ[ y-x ∈ Brw ] (x + y-x ≡ y))
isProp⟨BrwHasSubtraction⟩ {x} {y} = λ (z-x , p) (z-x' , q) → Σ≡Prop (λ z → Brw-is-set (x + z) _) (+-leftCancel x (p ∙ sym q))


splitting-≤-to-BrwHasSubtraction : splitting-≤ → BrwHasSubtraction
splitting-≤-to-BrwHasSubtraction split x y x≤y = Brw-ind (λ y → ∀ x → (x < y) ⊎ (x ≡ y) → Σ[ y-x ∈ Brw ] (x + y-x ≡ y))
  (λ z → isPropΠ2 (λ x _ → isProp⟨BrwHasSubtraction⟩))
  (λ { x (inl x<0) → ⊥.rec (succ≰zero x<0) ; x (inr x≡y) → (zero , x≡y) })
  (λ { ih x (inl x<sy) → let (y-x , p) = ih x (split (≤-succ-mono⁻¹ x<sy)) in (succ y-x) , cong succ p ; _ _ (inr x≡y) → (zero , x≡y) })
  (λ { {f} {f↑} ih x (inl x<limf) → ∥-∥rec isProp⟨BrwHasSubtraction⟩
                                          (λ (n , x<fn) → limitcase f f↑ ih x n x<fn ) (below-limit-lemma x f {f↑} x<limf) ; _ _ (inr x≡y) → (zero , x≡y) })
  y x (split x≤y)
  where
    limitcase : ∀ f (f↑ : increasing f) (ih : ∀ k x → (x < f k) ⊎ (x ≡ f k) → Σ-syntax Brw (λ y-x → x + y-x ≡ f k)) →
                ∀ x → (n : ℕ) → x < f n → Σ Brw (λ y-x → x + y-x ≡ limit f)
    limitcase f f↑ ih x n x<fn = (limit (λ k → fst (g k)) {increasing-fstg} ,
                                  limit-pointwise-equal (λ n → x + fst (g n)) (λ k → f (k N.+ n)) (λ k → snd (g k)) ∙ sym (limit-drop-initial n f {f↑}))
      where
        g : (k : ℕ) → Σ[ y-x ∈ Brw ] x + y-x ≡ f (k N.+ n)
        g k = ih (k N.+ n) x (split (<-in-≤ (<∘≤-in-< x<fn (increasing→monotone f↑ ((N.≤-+k {k = n} zero-≤))))))
        increasing-fstg : increasing (λ k → fst (g k))
        increasing-fstg k = +-leftCancel-< x (subst2 _<_ (sym (snd (g k))) (sym (snd (g (suc k)))) (f↑ (k N.+ n)))

splitting-≤-to-LPO : splitting-≤ → LPO
splitting-≤-to-LPO split s
  = map (lim⟨jumpSeq⟩<ω2→sk≡false s)
        (λ p → ∣ jumpSeq-translate-back s p ∣)
        (split {limit (jumpSeq s) {jumpSeq-increasing s}} (jumpSeq≤ω2 s))


unjump : (f : ℕ → Brw) → (P : Brw → Type)
         (decP : (n : ℕ) → Dec (P (f n))) → ℕ → Bool
unjump f P decP n = Dec→Bool (decP n)

unjump≡true-to-P : (f : ℕ → Brw)(P : Brw → Type)(decP : (n : ℕ) → Dec (P (f n))) →
              (k : ℕ) → unjump f P decP k ≡ true → P (f k)
unjump≡true-to-P f P decP k e with decP k
... | yes p = p
... | no ¬p = ⊥.rec (false≢true e)

unjump≡false-to-¬P : (f : ℕ → Brw)(P : Brw → Type)(decP : (n : ℕ) → Dec (P (f n))) →
              (k : ℕ) → unjump f P decP k ≡ false → ¬ P (f k)
unjump≡false-to-¬P f P decP k e with decP k
... | yes p = ⊥.rec (false≢true (sym e))
... | no ¬p = ¬p

P-to-unjump≡true : (f : ℕ → Brw)(P : Brw → Type)(decP : (n : ℕ) → Dec (P (f n))) →
              (k : ℕ) → P (f k) → unjump f P decP k ≡ true
P-to-unjump≡true f P decP k pfk with decP k
... | yes p = refl
... | no ¬p = ⊥.rec (¬p pfk)

¬P-to-unjump≡false : (f : ℕ → Brw)(P : Brw → Type)(decP : (n : ℕ) → Dec (P (f n))) →
              (k : ℕ) → ¬ P (f k) → unjump f P decP k ≡ false
¬P-to-unjump≡false f P decP k ¬pfk with decP k
... | yes p = ⊥.rec (¬pfk p )
... | no ¬p = refl


Dec¬ : {A : Type} → Dec A → Dec (¬ A)
Dec¬ (yes a) = no λ ¬a → ¬a a
Dec¬ (no ¬a) = yes ¬a

LPO→Dec≤ : LPO → ((x y : Brw) → Dec (x ≤ y))
LPO→Dec≤ lpo = Brw-ind (λ x → ∀ y → Dec (x ≤ y)) (λ x → isPropΠ (λ y → isPropDec isProp⟨≤⟩))
                       (λ y → yes ≤-zero)
                       (λ {x} ih → Brw-ind (λ y → Dec (succ x ≤ y)) (λ y → isPropDec isProp⟨≤⟩)
                                           (no succ≰zero)
                                           (λ {y} ih' → mapDec ≤-succ-mono (λ p q → p (≤-succ-mono⁻¹ q)) (ih y))
                                           λ {f} {f↑} ih' → Sum.rec (λ p → no λ x<lf → ∥-∥rec isProp⊥ (λ { (k , x<fk) → unjump≡false-to-¬P f (succ x ≤_) ih' k (p k) x<fk }) (below-limit-lemma x f x<lf))
                                                                    (∥-∥rec (isPropDec isProp⟨≤⟩) λ { (n , p) → yes (≤-cocone f (unjump≡true-to-P f (succ x ≤_) ih' n p)) })
                                                                    (lpo (unjump f (succ x ≤_) ih')))
                       (λ {f} {f↑} ih y → Sum.rec (λ p → yes (≤-limiting f λ k → Dec→Stable (ih k y)
                                                                                            (λ ¬fk≤y → unjump≡false-to-¬P f (λ z → ¬ (z ≤ y)) (λ n → Dec¬ (ih n y)) k (p k) ¬fk≤y)))
                                                  (∥-∥rec (isPropDec isProp⟨≤⟩) λ { (k , e) → no λ lf≤y → unjump≡true-to-P f (λ z → ¬ (z ≤ y)) (λ n → Dec¬ (ih n y)) k e
                                                                                                                          (≤-trans (≤-cocone-simple f {k = k}) lf≤y) })
                                                  (lpo (unjump f (λ z → ¬ (z ≤ y)) λ n → Dec¬ (ih n y))))

Dec≤→Dec< : ((x y : Brw) → Dec (x ≤ y)) → ((x y : Brw) → Dec (x < y))
Dec≤→Dec< d x y = d (succ x) y

LPO→Dec< : LPO → ((x y : Brw) → Dec (x < y))
LPO→Dec< lpo = Dec≤→Dec< (LPO→Dec≤ lpo)

Dec<→Decω< : ((x y : Brw) → Dec (x < y)) → ((y : Brw) → Dec (ω < y))
Dec<→Decω< d y = d ω y

Decω<→LPO : ((y : Brw) → Dec (ω < y)) → LPO
Decω<→LPO decω< s with decω< (limit (jumpSeq s) {jumpSeq-increasing s})
... | yes ω<lims↑ = inr ∣ jumpSeq-translate-back s (lim⟨jumpSeq⟩>ω→lim⟨jumpSeq⟩≡ω+ω s ω<lims↑) ∣
... | no ¬ω<lims↑ = inl λ k → Dec→Stable (s k ≟ false) λ sk≠false → ¬ω<lims↑ (subst (ω <_) (sym (jumpSeq-translate-forth s ∣ (k , ¬false→true (s k) sk≠false) ∣)) ω<ω+ω )


ω<ω·2 : ω < ω + ω
ω<ω·2 = ≤-cocone (λ n → ω + ι n) {_} {1} ≤-refl

sk≡false→lim⟨jumpSeq⟩≡ω : (s : ℕ → Bool)
  → (∀ k → s k ≡ false) → limit (jumpSeq s) {jumpSeq-increasing s} ≡ ω
sk≡false→lim⟨jumpSeq⟩≡ω s sk=false = ≤-antisym (≤-limiting (jumpSeq s) λ k → ≤-cocone ι (≤-refl-≡ (jumpSeq=ι k))) (ω-smallest (jumpSeq s))
  where
    some-below=false : (k : ℕ) → some-below s k ≡ false
    some-below=false zero = sk=false 0
    some-below=false (suc k) = cong₂ _or_ (sk=false (suc k)) (some-below=false k)
    jumpSeq=ι : (k : ℕ) → jumpSeq s k ≡ ι k
    jumpSeq=ι k =
      limit ι · (if some-below s k then succ zero else zero) + ι k
        ≡⟨ cong (λ z → limit ι · (if z then one else zero) + ι k) (some-below=false k) ⟩
      limit ι {ι-increasing} · zero + ι k
        ≡⟨ refl ⟩
      zero + ι k
        ≡⟨ zero+y≡y (ι k) ⟩
      ι k
        ∎

Dec≡ω→WLPO : ((x : Brw) → Dec (x ≡ ω)) → WLPO
Dec≡ω→WLPO dec s with dec (limit (jumpSeq s) {jumpSeq-increasing s})
... | yes p = inl (lim⟨jumpSeq⟩<ω2→sk≡false s (subst (_< ω + ω) (sym p) ω<ω·2))
... | no ¬p = inr (λ f → ¬p (sk≡false→lim⟨jumpSeq⟩≡ω s f))

WLPO→Dec≡ω : WLPO → (x : Brw) → Dec (x ≡ ω)
WLPO→Dec≡ω wlpo = Brw-ind (λ x → Dec (x ≡ ω))
                          (λ x → isPropDec (Brw-is-set x ω))
                          (no zero≠lim) (λ _ → no succ≠lim)
                          limit-case
 where
  limit-case : {f : ℕ → Brw} {f↑ : increasing f}
             → ((k : ℕ) → Dec (f k ≡ ω)) → Dec (limit f {f↑} ≡ ω)
  limit-case {f} {f↑} p = goal
   where
    ¬isFin : Brw → Type
    ¬isFin x = ¬ x < ω
    Dec¬isFin : ∀ i → Dec (¬isFin (f i))
    Dec¬isFin i = Dec¬ (Dec<ω (f i))
    g : ℕ → Bool
    g = unjump f ¬isFin Dec¬isFin
    g-all-false : (∀ i → g i ≡ false) → limit f {f↑} ≡ ω
    g-all-false gfalse = ≤-antisym lim-f≤ω (ω-smallest f)
     where
      f<ω : ∀ i → f i < ω
      f<ω i = Dec→Stable (Dec<ω (f i)) (unjump≡false-to-¬P f ¬isFin Dec¬isFin i (gfalse i))
      lim-f≤ω : limit f {f↑} ≤ ω
      lim-f≤ω = ≤-limiting f (λ i → <-in-≤ (f<ω i))
    g-not-all-false : ¬ (∀ i → g i ≡ false) → ¬ (limit f {f↑} ≡ ω)
    g-not-all-false ¬gfalse lim-f≡ω = ¬gfalse gfalse
     where
      f<ω : ∀ i → f i < ω
      f<ω i = subst (f i <_) lim-f≡ω (<-cocone-simple f)
      gfalse : ∀ i → g i ≡ false
      gfalse i = ¬P-to-unjump≡false f ¬isFin Dec¬isFin i (λ h → h (f<ω i))
    goal : Dec (limit f ≡ ω)
    goal with wlpo g
    ... | inl  gfalse = yes (g-all-false gfalse)
    ... | inr ¬gfalse = no (g-not-all-false ¬gfalse)

Dec× : {A B : Set} → Dec A → Dec B → Dec (A × B)
Dec× (yes a) (yes b) = yes (a , b)
Dec× (yes a) (no ¬b) = no (λ z → ¬b (snd z))
Dec× (no ¬a) (yes b) = no (λ z → ¬a (fst z))
Dec× (no ¬a) (no ¬b) = no (λ z → ¬b (snd z))

LPO→Dec≡ : LPO → ((x y : Brw) → Dec (x ≡ y))
LPO→Dec≡ lpo x y = mapDec (λ { (x≤y , y≤x) → ≤-antisym x≤y y≤x })
                          (λ p q → p ((≤-refl-≡ q) , ((≤-refl-≡ (sym q)))))
                          (Dec× (LPO→Dec≤ lpo x y) (LPO→Dec≤ lpo y x))

Dec≡→Dec≡ω·2 : ((x y : Brw) → Dec (x ≡ y)) → ((x : Brw) → Dec (x ≡ ω + ω))
Dec≡→Dec≡ω·2 d x = d x (ω + ω)

Dec≡ω·2→LPO : ((x : Brw) → Dec (x ≡ ω + ω)) → LPO
Dec≡ω·2→LPO dec s with dec (limit (jumpSeq s) {jumpSeq-increasing s})
... | yes p = inr ∣ jumpSeq-translate-back s p ∣
... | no ¬p = inl λ k → Dec→Stable (s k ≟ false) λ sk≠false → ¬p (jumpSeq-translate-forth s ∣ k , ¬false→true (s k) sk≠false ∣)

LPO→¬≤→> : LPO → (x y : Brw) → ¬ (x ≤ y) → y < x
LPO→¬≤→> lpo = Brw-ind (λ x → (y : Brw) → ¬ (x ≤ y) → y < x) (λ x → isPropΠ2 (λ y _ → isProp⟨<⟩))
                       (λ y p → ⊥.rec (p ≤-zero))
                       (λ {x} ih → Brw-ind (λ y → ¬ (succ x ≤ y) → y < succ x) (λ y → isProp→ isProp⟨<⟩)
                                           (λ _ → zero<succ)
                                           (λ {y} ihy p → <-succ-mono (ih y λ q → p (≤-succ-mono q)))
                                           λ {f} {f↑} → succlimCase x ih f f↑)
                       λ {f} {f↑} → limitCase f f↑
  where
    succlimCase : ∀ x (ih : ∀ y → ¬ (x ≤ y) → y < x) g (g↑ : increasing g) →
                 (ihy : ∀ k → ¬ (succ x ≤ g k) → g k < succ x) →
                 ¬ (succ x ≤ limit g) → limit g < succ x
    succlimCase x ih g g↑ ihy p = ≤∘<-in-< (≤-limiting g all-gn<x) <-succ-incr-simple
      where
        all-¬sx≤gn : (n : ℕ) → ¬ (succ x ≤ g n)
        all-¬sx≤gn n sx≤gn = p (≤-trans sx≤gn (≤-cocone-simple g))
        all-gn<x : (n : ℕ) → g n ≤ x
        all-gn<x n = ≤-succ-mono⁻¹ (ihy n (all-¬sx≤gn n))
    limitCase : ∀ f (f↑ : increasing f) →
                (ih : ∀ k y → ¬ (f k ≤ y) → y < f k) →
                ∀ y → ¬ (limit f ≤ y) → y < limit f
    limitCase f f↑ ih y p = <-trans _ _ _ (snd ∃y<fn) (<-cocone-simple f)
      where
        ¬∀fn≤y : ¬ ((n : ℕ) → f n ≤ y)
        ¬∀fn≤y q = p (≤-limiting f λ k → q k)
        ¬¬∃y<fn : ¬ ¬ (Σ[ n ∈ ℕ ] (y < f n))
        ¬¬∃y<fn q = ¬∀fn≤y (λ n → Dec→Stable (LPO→Dec≤ lpo _ _) λ p → q (n , ih n y p))
        ∃y<fn : Σ[ n ∈ ℕ ] (y < f n)
        ∃y<fn = map-snd (λ {n} → unjump≡true-to-P f (y <_) (λ n → LPO→Dec< lpo _ _) n) (LPO→MP lpo (unjump f (y <_) (λ n → LPO→Dec< lpo _ _)) (¬¬-functor (map-snd λ {n} → P-to-unjump≡true f (y <_) (λ n → LPO→Dec< lpo _ _) n) ¬¬∃y<fn))

LPO→¬<→≥ : LPO → (x y : Brw) → ¬ (x < y) → y ≤ x
LPO→¬<→≥ lpo x y p with LPO→Dec≤ lpo y x
... | yes y≤x = y≤x
... | no ¬y≤x = ⊥.rec (p (LPO→¬≤→> lpo y x ¬y≤x))

LPO→trichotomy : LPO → isTrichotomous _<_
LPO→trichotomy lpo x y with LPO→Dec< lpo x y
LPO→trichotomy lpo x y | yes x<y = inl x<y
LPO→trichotomy lpo x y | no ¬x<y with LPO→Dec< lpo y x
LPO→trichotomy lpo x y | no ¬x<y | yes y<x = inr (inl y<x)
LPO→trichotomy lpo x y | no ¬x<y | no ¬y<x = inr (inr (antisym' lpo x y ¬x<y ¬y<x))
  where
   antisym' : LPO → (x y : Brw) → ¬ (x < y) → ¬ (y < x) → x ≡ y
   antisym' lpo x y ¬x<y ¬y<x = ≤-antisym x≤y y≤x
    where
     contrapositive : {A B : Type} → (A → B) → ¬ B → ¬ A
     contrapositive f ¬b = λ z → ¬b (f z)
     x≤y : x ≤ y
     x≤y = Dec→Stable (LPO→Dec≤ lpo x y) (contrapositive (LPO→¬≤→> lpo x y) ¬y<x)
     y≤x : y ≤ x
     y≤x = Dec→Stable (LPO→Dec≤ lpo y x) (contrapositive (LPO→¬≤→> lpo y x) ¬x<y)

LPO→splitting≤ : LPO → splitting-≤
LPO→splitting≤ lpo = trichotomous→Splits-≤ <-irreflexive <∘≤-in-<
                                           (LPO→trichotomy lpo)

splitting-≤→trichotomy : splitting-≤ → isTrichotomous _<_
splitting-≤→trichotomy split = LPO→trichotomy (splitting-≤-to-LPO split)

trichotomy→splitting-≤ : isTrichotomous _<_ → splitting-≤
trichotomy→splitting-≤ tri = <∘≤-in-<→Splits-≤ <-irreflexive tri <∘≤-in-<

private
  -- alternative proof
  LPO→splitting≤' : LPO → splitting-≤
  LPO→splitting≤' lpo {x} {y} x≤y with LPO→Dec≡ lpo x y
  LPO→splitting≤' lpo {x} {y} x≤y | yes x=y = inr x=y
  LPO→splitting≤' lpo {x} {y} x≤y | no x≠y with  LPO→Dec< lpo x y
  LPO→splitting≤' lpo {x} {y} x≤y | no x≠y | yes x<y = inl x<y
  LPO→splitting≤' lpo {x} {y} x≤y | no x≠y | no ¬x<y = ⊥.rec (x≠y (≤-antisym x≤y (LPO→¬<→≥ lpo x y ¬x<y)))


has-sub→LPO : has-sub → LPO
has-sub→LPO = splitting-≤-to-LPO ∘ BrwHasSubtraction-to-splitting-≤ ∘ has-sub-to-BrwHasSubtraction

LPO→has-sub : LPO → has-sub
LPO→has-sub = BrwHasSubtraction-to-has-sub ∘ splitting-≤-to-BrwHasSubtraction ∘ LPO→splitting≤

Dec≡ωn→LPO : ∀ n → 2 N.≤ n → (∀ x → Dec (x ≡ ω · ι n)) → LPO
Dec≡ωn→LPO n 2≤n dec = Dec≡ω·2→LPO (subst (λ z → ∀ x → Dec (x ≡ z)) (x·2=x+x ω) (Dec≡ω2  n 2≤n dec))
  where
    step : ∀ n → (∀ x → Dec (x ≡ ω · ι (suc n))) → (∀ x → Dec (x ≡ ω · ι n))
    step n dec x = Dec≡a+y→Dec≡y ω (ω · ι n) (λ x → subst (λ z → Dec (x ≡ z)) (x·n=1=x+xn {n} ω) (dec x)) x
    Dec≡ω2 : ∀ n → 2 N.≤ n → (∀ x → Dec (x ≡ ω · ι n)) → (∀ x → Dec (x ≡ ω · ι 2))
    Dec≡ω2 zero 2≤0 dec = ⊥.rec (N.¬-<-zero 2≤0)
    Dec≡ω2 (suc zero) 2≤1 dec x = ⊥.rec (N.¬-<-zero (N.pred-≤-pred 2≤1))
    Dec≡ω2 (suc (suc zero)) 2≤n dec x = dec x
    Dec≡ω2 (suc (suc (suc n))) (zero , p) dec x = ⊥.rec (snotz (sym (injSuc (injSuc p))))
    Dec≡ω2 (suc (suc (suc n))) (suc k , p) dec x = Dec≡ω2 (suc (suc n)) (k , injSuc p) (step (suc (suc n)) dec) x
