{-# OPTIONS --cubical --erasure --guardedness #-}
module BrouwerTree.OrdinalDecidability.Basic where

open import Cubical.Data.Nat
  using (ℕ; zero; suc; ·-comm ; max ; +-zero ; +-suc ; isSetℕ)
  renaming (_+_ to _N+_; _·_ to _N·_; +-assoc to N+-assoc)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sigma hiding (∃; ∃-syntax)
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import BrouwerTree.Everything

open import PropTrunc
open import Iff
open import Bool as B
open import BooleanSequence
open import General-Properties


private
 variable
  ℓ ℓ' : Level

------------------ General definitions -------------

down-closed : (P : ℕ → Type ℓ) → Type ℓ
down-closed P = (n : ℕ) → P (suc n) → P n

up-closed : (P : ℕ → Type ℓ) → Type ℓ
up-closed P = (n : ℕ) → P n → P (suc n)

------------------ Definition of ordinal decidability -------------

ordinal-dec-str : (z : Brw) → (P : Type ℓ) → Type ℓ
ordinal-dec-str z P = Σ[ y ∈ Brw ] (P ↔ (z ≤ y))

ordinal-dec : (z : Brw) → (P : Type ℓ) → Type ℓ
ordinal-dec z P = ∥ ordinal-dec-str z P ∥


------------------ Definition of semidecidable proposition---------

semi-dec-str : (P : Type ℓ) → Type ℓ
semi-dec-str  P = Σ[ s ∈ (ℕ → Bool) ] (P ↔ (∃[ n ∈ ℕ ] s n ≡ true))

semi-dec :  (P : Type ℓ) → Type ℓ
semi-dec P  = ∥ semi-dec-str P ∥

dec→semi-dec : (P : Type ℓ) → Dec P → semi-dec-str P
dec→semi-dec P dec = (λ n → decRec (λ _ → true) (λ _ → false) dec) , f dec , g dec
 where
  f : (dec : Dec P) → P → ∃[ n ∈ ℕ ] decRec (λ _ → true) (λ _ → false) dec ≡ true
  f (yes p') p = ∣ 17 , refl ∣
  f (no ¬p) p = ⊥.rec (¬p p)

  g : (dec : Dec P) → ∃[ n ∈ ℕ ] decRec (λ _ → true) (λ _ → false) dec ≡ true → P
  g (yes p) _ = p
  g (no ¬p') q = ⊥.rec (∥-∥rec isProp⊥ (λ (_ , e) → false≢true e) q)

⊤-semi-dec-str : semi-dec-str Unit
⊤-semi-dec-str = dec→semi-dec Unit (yes tt)

⊥-semi-dec-str : semi-dec-str ⊥
⊥-semi-dec-str = dec→semi-dec ⊥ (no λ x → x)


∨-semi-dec : (P : Type ℓ) (Q : Type ℓ')
           → semi-dec P
           → semi-dec Q
           → semi-dec (∥ P ⊎ Q ∥)
∨-semi-dec P Q  = ∥-∥map2 [1]
 where
  [1] : semi-dec-str P  → semi-dec-str Q  → semi-dec-str ∥ P ⊎ Q ∥
  [1] (s , s-fwd , s-bwd) (t , t-fwd , t-bwd) =
   s⊕t , ∥-∥rec squash fwd , ∥-∥map bwd
    where
     or-one-of : {x y : Bool} → x or y ≡ true → (x ≡ true) ⊎ (y ≡ true)
     or-one-of {false} {y} e = inr e
     or-one-of {true} {y} e = inl refl
     s⊕t : ℕ → Bool
     s⊕t n = (s n) or (t n)
     fwd : P ⊎ Q → ∃[ n ∈ ℕ ] s⊕t n ≡ true
     fwd (inl p) =
      ∥-∥map (λ (n , e) → n , subst (λ - → - or (t n) ≡ true) (sym e) refl)
             (s-fwd p)
     fwd (inr q) =
      ∥-∥map
        (λ (n , e) → n , subst (λ - → s n or - ≡ true) (sym e) (or-zeroʳ (s n)))
        (t-fwd q)
     bwd : Σ ℕ (λ n → s⊕t n ≡ true) → P ⊎ Q
     bwd (n , h) with or-one-of h
     ... | inl e = inl (s-bwd ∣ (n , e) ∣)
     ... | inr e = inr (t-bwd ∣ (n , e) ∣)

∧-semi-dec-str : (P : Type ℓ) (Q : Type ℓ')
               → semi-dec-str P → semi-dec-str Q → semi-dec-str (P × Q)
∧-semi-dec-str P Q (s , s-fwd , s-bwd) (t , t-fwd , t-bwd) = s⊗t , fwd , bwd
 where
  open import Cubical.Data.Nat.Bijections.Product
  open import Cubical.Foundations.Isomorphism
  ϕ : ℕ → ℕ × ℕ
  ϕ = Iso.inv ℕ×ℕ≅ℕ
  ψ : ℕ × ℕ → ℕ
  ψ = Iso.fun ℕ×ℕ≅ℕ
  s⊗t : ℕ → Bool
  s⊗t n = s (fst (ϕ n)) and t (snd (ϕ n))
  fwd : P × Q → ∃[ n ∈ ℕ ] s⊗t n ≡ true
  fwd (p , q) = ∥-∥map2 h (s-fwd p) (t-fwd q)
   where
    h : Σ ℕ (λ n → s n ≡ true)
      → Σ ℕ (λ n → t n ≡ true)
      → Σ ℕ (λ n → s⊗t n ≡ true)
    h (n , e) (m , e') = ψ (n , m) , [2] ∙ [3]
     where
      [2] : s⊗t (ψ (n , m)) ≡ s n and t m
      [2] = subst2 (λ x y → (s x and t y) ≡ (s n and t m))
             (cong fst (sym (Iso.ret ℕ×ℕ≅ℕ (n , m))))
             (cong snd (sym (Iso.ret ℕ×ℕ≅ℕ (n , m))))
             refl
      [3] : (s n and t m) ≡ true
      [3] = subst2 (λ x y → x and y ≡ true) (sym e) (sym e') refl
  bwd : ∃[ n ∈ ℕ ] s⊗t n ≡ true → P × Q
  bwd = (λ t → h₁ t , h₂ t)
   where
    and-both : {x y : Bool} → x and y ≡ true → (x ≡ true) × (y ≡ true)
    and-both {false} {y} e =
     ⊥.elim {_} {λ _ → (false ≡ true) × (y ≡ true)} (false≢true e)
    and-both {true} {false} e =
     ⊥.elim {_} {λ _ → (true ≡ true) × (false ≡ true)} (false≢true e)
    and-both {true} {true} _ = refl , refl
    h₁ : ∃[ n ∈ ℕ ] s⊗t n ≡ true → P
    h₁ t = s-bwd (∥-∥map (λ (n , e) → fst (ϕ n) , fst (and-both e)) t)
    h₂ : ∃[ n ∈ ℕ ] s⊗t n ≡ true → Q
    h₂ t = t-bwd (∥-∥map (λ (n , e) → snd (ϕ n) , snd (and-both e)) t)

∧-semi-dec : (P : Type ℓ) (Q : Type ℓ')
           → semi-dec P → semi-dec Q → semi-dec (P × Q)
∧-semi-dec P Q = ∥-∥map2 (∧-semi-dec-str P Q)

∃-semi-dec-str : (P : ℕ → Type ℓ)
               → ((n : ℕ) → semi-dec-str (P n))
               → semi-dec-str (∃ ℕ P)
∃-semi-dec-str P σ = s ∘ ϕ , ↔-trans γ (∥-∥↔ (γ' , γ''))
 where
  open import Cubical.Data.Nat.Bijections.Product
  open import Cubical.Foundations.Isomorphism
  ϕ : ℕ → ℕ × ℕ
  ϕ = Iso.inv ℕ×ℕ≅ℕ
  ψ : ℕ × ℕ → ℕ
  ψ = Iso.fun ℕ×ℕ≅ℕ

  s : ℕ × ℕ → Bool
  s (n , m) = fst (σ n) m
  s-spec : (n : ℕ) → P n ↔ ∃[ m ∈ ℕ ] s (n , m) ≡ true
  s-spec n = snd (σ n)
  γ : ∃ ℕ P ↔ ∃[ n ∈ ℕ ] Σ[ m ∈ ℕ ] s (n , m) ≡ true
  γ = [1] , [2]
   where
    [1] : ∃ ℕ P → ∃[ n ∈ ℕ ] Σ[ m ∈ ℕ ] s (n , m) ≡ true
    [1] = ∥-∥rec isPropPropTrunc
                 (λ (n , p) → ∥-∥map (λ (m , e) → n , m , e) (lr (s-spec n) p) )
    [2] : ∃[ n ∈ ℕ ] Σ[ m ∈ ℕ ] s (n , m) ≡ true → ∃ ℕ P
    [2] = ∥-∥map λ (n , m , e) → n , rl (s-spec n) ∣ m , e ∣
  γ' : Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] s (n , m) ≡ true → Σ[ n ∈ ℕ ] s (ϕ n) ≡ true
  γ' (n , m , e) = ψ (n , m) , cong s (Iso.ret ℕ×ℕ≅ℕ (n , m)) ∙ e

  γ'' : Σ[ n ∈ ℕ ] s (ϕ n) ≡ true → Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] s (n , m) ≡ true
  γ'' (n , e) = _ , _ , cong (s ∘ ϕ) (Iso.sec ℕ×ℕ≅ℕ n) ∙ e

semi-dec-str-stable-under-↔ : (P : Type ℓ) (Q : Type ℓ')
                            → (P ↔ Q)
                            → (semi-dec-str P ↔ semi-dec-str Q)
semi-dec-str-stable-under-↔ P Q (f , g) = [1] P Q f g , [1] Q P g f
 where
  [1] : (P : Type ℓ) (Q : Type ℓ')
      → (P → Q) → (Q → P)
      → semi-dec-str P → semi-dec-str Q
  [1] P Q f g (β , (d₀ , d₁)) = (β , (d₀ ∘ g , f ∘ d₁))

semi-dec-stable-under-↔ : (P : Type ℓ) (Q : Type ℓ')
                        → (P ↔ Q)
                        → (semi-dec P ↔ semi-dec  Q)
semi-dec-stable-under-↔  P Q e =
 (∥-∥map (lr (semi-dec-str-stable-under-↔ P Q e)) ,
  ∥-∥map (rl (semi-dec-str-stable-under-↔ P Q e)))

semi-dec-sim : (P : Type ℓ)
             → ((s , q) (s' , q') : semi-dec-str P)
             → (k : ℕ) → ∃[ m ∈ ℕ ] s k B≤ s' m
semi-dec-sim P (s , q) (s' , q') k = aux (s k) refl
 where
  aux : (y : Bool) → y ≡ s k → ∃[ m ∈ ℕ ] y B≤ s' m
  aux false e = ∣ 17 , tt ∣
  aux true e = ∥-∥map (map-snd λ p → Bool≡→≤ (sym p))
                      ((lr q' (rl q ∣ k , sym e ∣)))

LPO' : (ℓ : Level) → Type (ℓ-suc ℓ)
LPO' ℓ = (P : Type ℓ) → isProp P → semi-dec P → Dec P

LPO'→LPO : LPO' ℓ-zero → LPO
LPO'→LPO lpo' s = decRec inr (inl ∘ [2]) [1]
 where
  [1] : Dec (∃[ n ∈ ℕ ] s n ≡ true)
  [1] = lpo' (∃[ n ∈ ℕ ] s n ≡ true) isPropPropTrunc ∣ (s , ↔-refl) ∣
  [2] : ¬ (∃[ n ∈ ℕ ] s n ≡ true) → (k : ℕ) → s k ≡ false
  [2] h k = ¬true→false (s k) (λ e → h ∣ k , e ∣)

MP' : (ℓ : Level) → Type (ℓ-suc ℓ)
MP' ℓ = (P : Type ℓ) → isProp P → semi-dec P → ¬ ¬ P → P

MP→MP' : MP → MP' ℓ
MP→MP' mp P P-prop σ ¬¬P = ∥-∥rec P-prop [1] σ
 where
  [1] : semi-dec-str P → P
  [1] (s , ρ) = rl ρ ∣ mp s (¬¬-functor [2] (¬¬-functor (lr ρ) ¬¬P)) ∣
   where
    [2] : ∃[ n ∈ ℕ ] s n ≡ true → Σ[ n ∈ ℕ ] s n ≡ true
    [2] = least-witness (λ n → s n ≡ true) (λ n → isSetBool _ _) (λ n → s n ≟ true)

-----------------First Observation Toward Ordinal Decidability:-----------------
--Proposition: P is decidable iff it is ω-decidable iff it is finite-decidable.

dec↔ω-dec : (P : Type ℓ) → isProp P → (Dec P ↔ ordinal-dec ω P)
dec↔ω-dec P  P-prop = [1] , [2]
 where
  [1] : Dec P → ordinal-dec ω P
  [1] (yes p) = ∣ ω , (λ _ → ≤-refl) , (λ _ → p) ∣
  [1] (no ¬p) = ∣ zero , (λ p → ⊥.elim (¬p p)) , (λ l → ⊥.elim (lim≰zero l)) ∣
  [2] : ordinal-dec ω P  → Dec P
  [2] h = ∥-∥rec (isPropDec P-prop) [3] h
   where
    [3] : ordinal-dec-str ω P → Dec P
    [3] (x , f , g) = κ (<ω-or-≥ω x)
     where
      κ : (x < ω) ⊎ (ω ≤ x) → Dec P
      κ (inl l) = no (λ p → <-irreflexive x (<∘≤-in-< l (f p)))
      κ (inr l) = yes (g l)

dec↔1-dec : (P : Type ℓ) → isProp P
          → Dec P ↔ ordinal-dec one P
dec↔1-dec P i = [1] , [2]
 where
  [1] : Dec P → ordinal-dec one P
  [1] (yes p) = ∣ one , (λ _ → ≤-refl) , (λ _ → p) ∣
  [1] (no ¬p) = ∣ zero , (λ p → ⊥.elim (¬p p)) , (λ l → ⊥.elim (succ≰zero l)) ∣
  [2] : ordinal-dec one P → Dec P
  [2] = ∥-∥rec (isPropDec i) [3]
   where
    [3] : ordinal-dec-str one P → Dec P
    [3] (x , f , g) = mapDec g (λ ν p → ν (f p)) (dec-n≤ x 1)

dec↔fin-dec : (P : Type ℓ) → isProp P
            → Dec P ↔ (Σ[ n ∈ ℕ ] ordinal-dec (ι (suc n)) P)
dec↔fin-dec P P-is-prop = [1] , [2]
 where
  [1] : Dec P → Σ[ n ∈ ℕ ] ordinal-dec (ι (suc n)) P
  [1] (yes p) = 1 , ∣ ι 2 , (λ _ → ≤-refl) , (λ _ → p) ∣
  [1] (no ¬p) = 1 , ∣ zero , (λ p → ⊥.elim (¬p p)) , (λ l → ⊥.elim (succ≰zero l)) ∣
  [2] : Σ ℕ (λ n → ordinal-dec (ι (suc n)) P) → Dec P
  [2] (n , h) = ∥-∥rec (isPropDec P-is-prop) [3] h
   where
    [3] : ordinal-dec-str (ι (suc n)) P → Dec P
    [3] (x , f , g) = mapDec g (λ ν p → ν (f p)) (dec-n≤ x (suc n))

semidec↔ω+1-dec : (P : Type ℓ) → isProp P
                → semi-dec P ↔ ordinal-dec (succ ω) P
semidec↔ω+1-dec P P-is-prop = ∥-∥map semidec→ω+1-dec ,
                              ∥-∥rec isPropPropTrunc ω+1-dec→semidec
 where
  semidec→ω+1-dec : semi-dec-str P → ordinal-dec-str (succ ω) P
  semidec→ω+1-dec (s , ρ) = limit[ s ]↑ , [1] , [2]
   where
    [1] : P → ω < limit[ s ]↑
    [1] p = subst (ω <_) (sym (jumpSeq-translate-forth s (lr ρ p))) ω<ω·2
    [2] : ω < limit[ s ]↑ → P
    [2] l = rl ρ ∣ jumpSeq>ω-translate-back s l ∣

  ω+1-dec→semidec : ordinal-dec-str (succ ω) P → semi-dec P
  ω+1-dec→semidec (x , ρ) = Brw-ind (λ x → P ↔ ω < x → semi-dec P)
                                    (λ x → isProp→ isPropPropTrunc)
                                    [1]
                                    [2]
                                    (λ {f} {f↑} → [3] {f} {f↑})
                                    x ρ
   where
    [1] : P ↔ (ω < zero) → semi-dec P
    [1] τ = ∣ (λ _ → false) , ↔-trans τ ([1]₁ , ∥-∥rec isProp⟨<⟩ [1]₂) ∣
     where
      [1]₁ : ω < zero → ∃[ n ∈ ℕ ] false ≡ true
      [1]₁ l = ⊥.rec (x≮zero l)
      [1]₂ : Σ[ n ∈ ℕ ] false ≡ true → ω < zero
      [1]₂ (_ , e) = ⊥.rec (false≢true e)
    [2] : {y : Brw} → (P ↔ (ω < y) → semi-dec P)
        → P ↔ (ω < succ y) → semi-dec P
    [2] {y} ih τ = lr (semi-dec-stable-under-↔ (¬ isFinite y) P [2]₁) [2]₂
     where
      [2]₁ : ¬ isFinite y ↔ P
      [2]₁ = ↔-trans (notFinite-correct-↔ y) (↔-sym (↔-trans τ ≤-succ-mono-↔))
      [2]₂ : semi-dec (¬ isFinite y)
      [2]₂ = ∣ (dec→semi-dec (¬ isFinite y) (Dec¬ (decIsFinite y))) ∣
    [3] : {f : ℕ → Brw} {f↑ : increasing f}
        → ((k : ℕ) → P ↔ (ω < f k) → semi-dec P)
        → P ↔ (ω < limit f) → semi-dec P
    [3] {f} {f↑} ih τ = ∣ g , ↔-trans τ [3]₁ ∣
     where
      d : (n : ℕ) → Dec (¬ isFinite (f n))
      d n = Dec¬ (decIsFinite (f n))
      g : ℕ → Bool
      g = unjump f (¬_ ∘ isFinite) d
      [3]₁ : ω < limit f ↔ ∃[ n ∈ ℕ  ] g n ≡ true
      [3]₁ = ↔-trans (below-limit-↔ ω f) (∥-∥↔ ([3]₂₋₁ , [3]₂₋₂))
       where
        [3]₂₋₁ : Σ[ n ∈ ℕ  ] ω < f n → Σ[ n ∈ ℕ  ] g n ≡ true
        [3]₂₋₁ (n , l) = n , P-to-unjump≡true f (¬_ ∘ isFinite) d n
                                              (rl (notFinite-correct-↔ (f n))
                                                  (<-in-≤ l))

        [3]₂₋₂ : Σ[ n ∈ ℕ  ] g n ≡ true → Σ[ n ∈ ℕ  ] ω < f n
        [3]₂₋₂ (n , e) = (suc n , ≤∘<-in-< [3]₂-₃ (f↑ n))
         where
          [3]₂₋₃ : ¬ isFinite (f n)
          [3]₂₋₃ = unjump≡true-to-P f (¬_ ∘ isFinite) d n e
          [3]₂-₃ : ω ≤ f n
          [3]₂-₃ = lr (notFinite-correct-↔ (f n)) [3]₂₋₃

∃∃dec-is-semidec : (P : ℕ → ℕ → Type ℓ)
                 → ((n m : ℕ) → Dec (P n m))
                 → semi-dec (∃[ n ∈ ℕ ] Σ[ m ∈ ℕ ] P n m)
∃∃dec-is-semidec P Pdec = ∣ s , ∥-∥rec isPropPropTrunc [1] , ∥-∥map [2] ∣
 where
  open import Cubical.Data.Nat.Bijections.Product
  open import Cubical.Foundations.Isomorphism
  ϕ : ℕ → ℕ × ℕ
  ϕ = Iso.inv ℕ×ℕ≅ℕ
  ψ : ℕ × ℕ → ℕ
  ψ = Iso.fun ℕ×ℕ≅ℕ
  s : ℕ → Bool
  s n = Dec→Bool (Pdec (fst (ϕ n)) (snd (ϕ n)))

  [1] : Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] P n m → ∃[ k ∈ ℕ ] s k ≡ true
  [1] (n , t) = ∣  [1]' t ∣
   where
    [1]' : Σ ℕ (P n) → Σ[ k ∈ ℕ ] s k ≡ true
    [1]' (m , p) = (ψ (n , m) , e)
     where
      e = s (ψ (n , m))       ≡⟨ cong₂ (λ x y → Dec→Bool (Pdec x y)) e₁ e₂ ⟩
          Dec→Bool (Pdec n m) ≡⟨ Dec→Bool≡true (P n m) p (Pdec n m) ⟩
          true                ∎
       where
        e₁ = cong fst (Iso.ret ℕ×ℕ≅ℕ (n , m))
        e₂ = cong snd (Iso.ret ℕ×ℕ≅ℕ (n , m))

  [2] : Σ[ k ∈ ℕ ] s k ≡ true → Σ[ n ∈ ℕ ] Σ ℕ (P n)
  [2] (k , e) = n ,  (m , toWitness P-holds)
   where
    n = fst (ϕ k)
    m = snd (ϕ k)
    P-holds : True (Pdec n m)
    P-holds = subst Bool→Type (sym e) tt

------------------

finite-decidability-all-equivalent
 : (P : Type ℓ) (n m : ℕ)
 → ordinal-dec (ι (suc n)) P ↔ ordinal-dec (ι (suc m)) P
finite-decidability-all-equivalent P n m = wlog n m , wlog m n
 where
  wlog : (n m : ℕ) → ordinal-dec (ι (suc n)) P → ordinal-dec (ι (suc m)) P
  wlog n m = ∥-∥map [1]
   where
    [1] : ordinal-dec-str (ι (suc n)) P  → ordinal-dec-str (ι (suc m)) P
    [1] (u , g) = [2] (dec-n≤ u (suc n))
     where
      [2] : Dec (ι (suc n) ≤ u) → ordinal-dec-str (ι (suc m)) P
      [2] (yes u≤n) = ι (suc m) , (λ _ → ≤-refl) , (λ _ → rl g u≤n)
      [2] (no ¬u≤n) =
       ι m , (λ p → ⊥.rec (¬u≤n (lr g p))) , λ l → ⊥.rec (<-irreflexive (ι m) l)

zero-decidable-str-iff-true : (P : Type ℓ) → ordinal-dec-str zero P ↔ P
zero-decidable-str-iff-true P = [1] , [2]
 where
  [1] : ordinal-dec-str zero P → P
  [1] (u , g) = rl g ≤-zero

  [2] : P → ordinal-dec-str zero P
  [2] p = zero , (λ _ → ≤-refl) , (λ _ → p)

zero-decidable-iff-true : (P : Type ℓ) → isProp P → ordinal-dec zero P ↔ P
zero-decidable-iff-true P P-prop =
 ∥-∥rec P-prop (lr (zero-decidable-str-iff-true P)) ,
 ∣_∣ ∘ rl (zero-decidable-str-iff-true P)

---------------------- Second Observation Toward Ordinal Decidability:-------------
-- Proposition: a proposition P is semidecidable if and only if it is ω·2-decidable.

semidec→ω·2dec : (P : Type ℓ) → isProp P → semi-dec P → ordinal-dec (ω + ω) P
semidec→ω·2dec P P-prop = ∥-∥map h
 where
  h :  semi-dec-str P  → ordinal-dec-str (ω + ω)  P
  h (s , (g₁ , g₂)) = α , (q₁ , q₂)
   where
     f : ℕ → Brw
     f zero = zero
     f (suc n) with s n ≟ true
     ... | yes _ = f n + ω
     ... | no _ = f n + ι 1
     f-eq₀ : f 0 ≡ zero
     f-eq₀ = refl
     f-eq₁ : (n : ℕ) → s n ≡ true → f (suc n) ≡ f n + ω
     f-eq₁ n e with s n ≟ true
     ... | yes _ = refl
     ... | no  ν = ⊥.rec (ν e)
     f-eq₂ : (n : ℕ) → s n ≡ false → f (suc n) ≡ succ (f n)
     f-eq₂ n e with s n ≟ true
     ... | yes e' = ⊥.rec (true≢false (sym e' ∙ e))
     ... | no  _ = refl
     f↑ : increasing f
     f↑ k  with s k ≟ true
     ... | yes _ = ≤-cocone (λ n → f k + ι n) {k = 1} ≤-refl
     ... | no _ = ≤-refl
     α : Brw
     α = limit f {f↑}

     q₁ : P → (ω + ω) ≤ α
     q₁ e = ∥-∥rec ≤-trunc M (g₁ e)
      where
       M :  Σ[ n ∈ ℕ ] s n ≡ true → ω + ω ≤ α
       M (n₀ , sn0=t) = simulation→≤ Hsim
        where
          v : ω ≤ f (suc n₀)
          v with s n₀ ≟ true
          ... | yes z = ω-smallest (λ n → f (n₀) + ι n)
          ... | no  z' = ⊥.rec (z' sn0=t)
          Hsim : (k : ℕ) → Σ[ n ∈ ℕ ] ω + ι k ≤ f n
          Hsim k  = (suc n₀ N+ k , hN₀)
            where
              hN₀ : ω + ι k ≤ f (suc n₀ N+ k)
              hN₀ = ≤-offset-by-ι f {f↑} ω v

     q₂ : ω + ω ≤ α → P
     q₂ a  = ∥-∥rec P-prop M L
      where
       L :  ∃[ n ∈ ℕ ] ω ≤ f n
       L = lim≤lim→weakly-bisimilar (λ u → ω + ι u) f a zero
       M : Σ[ n ∈ ℕ ] ω ≤ f n → P
       M (n , b) = g₂ (∥-∥map (λ (k , _ , e) → k , e) w)
        where
         w :  ∃[ k ∈ ℕ ] (k N.≤ n) × (s k ≡ true)
         w = δ n b
          where
           δ : (n : ℕ) → ω ≤ f n → ∃[ k ∈  ℕ ] (k N.≤ n) × (s k ≡ true)
           δ zero l = ⊥.elim (lim≰zero l)
           δ (suc n) l with dec-true-below n s
           ... | yes (k , l , e) = ∣ k , N.≤-suc l , e ∣
           ... | no v' = ∥-∥map (λ (k , l , e) → k , N.≤-suc l , e) (δ n [3])
            where
             [1] : s n ≡ false
             [1] = ¬true→false (s n) (λ (e : s n ≡ true) → v' (n , N.≤-refl , e))
             [2] : ω ≤ succ (f n)
             [2] = subst (ω ≤_) (f-eq₂ n [1]) l
             [3] : ω ≤ f n
             [3] = lim≤sx→lim≤x ι (f n) [2]

ω·2dec→semidec : (P : Type ℓ) → isProp P → ordinal-dec (ω + ω) P → semi-dec P
ω·2dec→semidec {ℓ} P P-prop = ∥-∥rec isPropPropTrunc f
 where
  f : ordinal-dec-str (ω + ω) P → semi-dec P
  f (X , (b₁ , b₂)) = F X b₁ b₂
   where
    F : (x : Brw) → (β₁ : P → ω + ω ≤ x) → (β₂ : ω + ω ≤ x → P) → semi-dec P
    F = Brw-ind PF (λ x → isProp→ (isProp→ isPropPropTrunc))  P₀ Pₛ Pₗ
     where
         PF : Brw → Type ℓ
         PF x = (P → ω + ω ≤ x) → (ω + ω ≤ x → P) → semi-dec P

         P₀ : PF zero
         P₀ β₁ β₂ = ∣ (λ _ → false) , [1] , [2] ∣
          where
           [1] : P → ∃[ n ∈ ℕ ] false ≡ true
           [1] p = ⊥.rec (lim≰zero (β₁ p))
           [2] : ∃[ n ∈ ℕ ] false ≡ true → P
           [2] = ∥-∥rec P-prop (λ (n , e) → ⊥.rec (false≢true e))

         Pₛ : {x : Brw} → PF x → PF (succ x)
         Pₛ {x} IH β₁ β₂ = ∥-∥map (λ σ → σ) (IH ([1] ∘ β₁) (β₂ ∘ [2]))
          where
           [1] : ω + ω ≤ succ x → ω + ω ≤ x
           [1] = lim≤sx→lim≤x (λ n → ω + ι n) x
           [2] : ω + ω ≤ x → ω + ω ≤ succ x
           [2] = ≤-succ-incr

         Pₗ : {g : ℕ → Brw} {g↑ : increasing g}
            → ((k : ℕ) → PF (g k)) → PF (limit g {g↑})
         Pₗ {g} {g↑} _ β₁ β₂ = ∣ s , γ₁ , γ₂ ∣
           where
            s : ℕ → Bool
            s zero = false
            s (suc k) with <ω-or-≥ω (g k)
            ... | inl gk<ω = false
            ... | inr ω≤gk = true
            s-eq₁ : (k : ℕ) → g k < ω → s (suc k) ≡ false
            s-eq₁ k l with <ω-or-≥ω (g k)
            ... | inl _ = refl
            ... | inr ω≤gk = ⊥.elim (<-irreflexive (g k) (<∘≤-in-< l ω≤gk))
            s-eq₂ : (k : ℕ) → ω ≤ g k → s (suc k) ≡ true
            s-eq₂ k l with <ω-or-≥ω (g k)
            ... | inl gk<ω = ⊥.elim (<-irreflexive ω (≤∘<-in-< l gk<ω))
            ... | inr _ = refl
            s-eq₃ : (k : ℕ) → s (suc k) ≡ true → ω ≤ g k
            s-eq₃ k e with <ω-or-≥ω (g k)
            ... | inl _ = ⊥.elim {_} {λ _ → ω ≤ g k} (false≢true e)
            ... | inr ω≤gk = ω≤gk
            γ₁ : P → ∃[ n ∈ ℕ ] s n ≡ true
            γ₁ p = ∥-∥map [3] ([2] 0)
             where
              [1] : ω + ω ≤ limit g
              [1] = β₁ p
              [2] : (k : ℕ) → ∃[ n ∈ ℕ ] ω + ι k ≤ g n
              [2] = lim≤lim→weakly-bisimilar (λ n → ω + ι n) g [1]
              [3] : Σ[ n ∈ ℕ ] ω ≤ g n → Σ[ n ∈ ℕ ] s n ≡ true
              [3] (n , l) = (suc n , s-eq₂ n l)
            γ₂ : ∃[ n ∈ ℕ ] s n ≡ true → P
            γ₂ = ∥-∥rec P-prop (β₂ ∘  ϕ)
             where
              ϕ : Σ[ n ∈ ℕ ] s n ≡ true → ω + ω ≤ limit g
              ϕ (zero , e) = ⊥.rec (false≢true e)
              ϕ (suc n , e) = [3]
               where
                [1] : ω ≤ g n
                [1] = s-eq₃ n e
                [2] : (k : ℕ) → ω + ι k ≤ g (n N+ k)
                [2] k = ≤-offset-by-ι g {g↑} ω [1]
                [3] : ω + ω ≤ limit g {g↑}
                [3] = weakly-bisimilar→lim≤lim _ _ (λ k → ∣ n N+ k , [2] k ∣)

---------------Definition of Brwᶻˡ----------------

Brw-zero-or-limit  : (x : Brw) → Type
Brw-zero-or-limit x = is-lim x ⊎ (x ≡ zero)

isPropBrw-zero-or-limit : (x : Brw) → isProp (Brw-zero-or-limit x)
isPropBrw-zero-or-limit x =
 isProp⊎ isProp⟨is-lim⟩
         (Brw-is-set _ _)
         (λ l z → unique.not-z-and-l x (≡zero→is-zero z) l)

Brwᶻˡ : Type
Brwᶻˡ = Σ[ x ∈ Brw ] (Brw-zero-or-limit x)
