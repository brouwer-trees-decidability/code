----------------------------------------------------------------------------------------------------
-- Properties of arithmetic operations on Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Arithmetic.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
  using (ℕ; zero; suc; +-zero; +-suc; ·-comm; +-comm)
  renaming (_+_ to _N+_; _·_ to _N·_; +-assoc to N+-assoc)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary using (Dec; yes; no)

open import Iff
open import PropTrunc

open import BrouwerTree.Base
open import BrouwerTree.Properties
open import BrouwerTree.Code
open import BrouwerTree.Code.Results
open import BrouwerTree.Arithmetic
open import BrouwerTree.Classifiability


{- More general lemmas -}

N≤-k· : ∀ {m n k} → m N.≤ n → k N· m N.≤ k N· n
N≤-k· {m} {n} {k} m≤n = subst (λ z → fst z N.≤ snd z)
                              (λ i → ·-comm m k i , ·-comm n k i)
                              (N.≤-·k m≤n)

ι-+-commutes : ∀ n m → ι (m N+ n) ≡ ι n + ι m
ι-+-commutes n zero = refl
ι-+-commutes n (suc m) = cong succ (ι-+-commutes n m)

ι-+-commutes' : ∀ n m → ι (n N+ m) ≡ ι n + ι m
ι-+-commutes' n m = cong ι (+-comm n m) ∙ (ι-+-commutes n m)

ι-·-commutes : ∀ n m → ι (m N· n) ≡ ι n · ι m
ι-·-commutes n zero = refl
ι-·-commutes n (suc m) = ι-+-commutes (m N· n) n ∙ cong (_+ ι n) (ι-·-commutes n m)

ι-succ : (x : Brw) → (n : ℕ) → succ x + ι n ≡ x + ι (suc n)
ι-succ x zero = refl
ι-succ x (suc n) = cong succ (ι-succ x n)

increasing-≤→monotone : ∀ {f : ℕ → Brw} → ((m : ℕ) → f m ≤ f (suc m)) → ∀ {n m} → n N.≤ m → f n ≤ f m
increasing-≤→monotone {f} f↑ {n} {m} (k , k+n≡m) = helper {n} {m} k k+n≡m where
  helper : ∀ {n} {m} → (k : ℕ) → k N+ n ≡ m → f n ≤ f m
  helper zero n≡m = ≤-refl-≡ (cong f n≡m)
  helper {n} {m} (suc k) sk+n≡m = subst (λ z → f n ≤ f z) sk+n≡m
                                        (≤-trans (helper k refl) (f↑ (k N+ n)))

increasing→monotone : ∀ {f : ℕ → Brw} → increasing f → ∀ {n m} → n N.≤ m → f n ≤ f m
increasing→monotone {f} f↑ = increasing-≤→monotone (λ m → <-in-≤ (f↑ m))

increasing→zero<fsuc : ∀ {f : ℕ → Brw} {k} → increasing f → zero < f (suc k)
increasing→zero<fsuc {f} {zero} f↑ = ≤∘<-in-< ≤-zero (f↑ 0)
increasing→zero<fsuc {f} {suc k} f↑ = <-trans _ _ _ (increasing→zero<fsuc {f} {k} f↑) (f↑ (suc k))

succ-from : Brw → ℕ → Brw
succ-from x zero = x
succ-from x (suc n) = succ (succ-from x n)

succ-from-increasing : {x : Brw} → increasing (succ-from x)
succ-from-increasing zero = ≤-refl
succ-from-increasing (suc k) = ≤-succ-mono (succ-from-increasing k)

{- Lemmas about properties of arithmetic operations -}

+-assoc : ∀ {a b} c → a + (b + c) ≡ (a + b) + c
+-assoc {a} {b} =
  Brw-ind (λ c → a + (b + c) ≡ (a + b) + c)
          (λ c → Brw-is-set _ _)
          refl
          (λ {x} ih → cong succ ih)
          (λ {f} {f↑} ih → limit-pointwise-equal _ _ ih)

·-+-distributivity : ∀ {a b} c → a · b + a · c ≡ a · (b + c)
·-+-distributivity {a} {b} =
  Brw-ind (λ c → a · b + a · c ≡ a · (b + c))
          (λ c → Brw-is-set _ _)
          refl
          (λ {x} ih → +-assoc {a · b} {a · x} a ∙ cong (_+ a) ih)
          limitCase
 where
  limitCase : ∀ {f} {f↑} → (∀ k → a · b + a · f k ≡ a · (b + f k)) →
                a · b + a · limit f {f↑} ≡ a · (b + limit f {f↑})
  limitCase {f} {f↑} ih with decZero a
  ... | yes a≡zero = cong (_· b) a≡zero ∙ zero·y≡zero b
  ... | no a≡zero = limit-pointwise-equal _ _ ih

x<lim→x+n<lim : ∀ f x {f↑} n → x < limit f {f↑} → (x + ι n) < limit f {f↑}
x<lim→x+n<lim f x zero l = l
x<lim→x+n<lim f x (suc n) l = subst (_< limit f) eq ih
 where
  ih : (succ x + ι n) < limit f
  ih = x<lim→x+n<lim f (succ x) n (x<lim→sx<lim f x l)
  eq : succ x + ι n ≡ x + ι (suc n)
  eq = ι-succ x n

x+-strictly-increasing : ∀ {x} (z : Brw) → (z ≡ zero → ⊥) → x < x + z
x+-strictly-increasing {x} = Brw-ind _ (λ _ → isProp→ <-trunc) P₀ Pₛ Pₗ
 where
  P₀ : (zero ≡ zero → ⊥) → x < x + zero
  P₀ e = ⊥.rec (e refl)
  Pₛ : {z : Brw}
     → ((z ≡ zero → ⊥) → x < x + z)
     → (succ z ≡ zero → ⊥) → x < succ (x + z)
  Pₛ {z} _ _ = ≤-succ-mono (x+-increasing z)
  Pₗ : {f : ℕ → Brw} {f↑ : increasing f}
     → ((k : ℕ) → (f k ≡ zero → ⊥) → x < x + f k)
     → (limit f {f↑} ≡ zero → ⊥) → x < limit (λ n → x + f n)
  Pₗ {f} {f↑} IH _ = ≤-trans [2] (≤-cocone (λ n → x + f n) ≤-refl)
   where
    [1] : f 1 ≡ zero → ⊥
    [1] e = x≮zero (subst (f 0 <_) e (f↑ 0))
    [2] : succ x ≤ x + f 1
    [2] = IH 1 [1]

add-finite-part-lemma' : (f : ℕ → Brw) {f↑ : increasing f} (n k : ℕ)
                       → f n + ι k ≤ f (n N+ k)
add-finite-part-lemma' f {f↑} n zero = transport (cong (λ - → f n ≤ f -) (sym (+-zero n))) ≤-refl
add-finite-part-lemma' f {f↑} n (suc k) =
 ≤-trans (≤-succ-mono (add-finite-part-lemma' f {f↑} n k))
         (transport (cong (λ - → succ (f (n N+ k)) ≤ f -) (sym (+-suc n k))) (f↑ (n N+ k)))

add-finite-part-lemma : (f : ℕ → Brw) {f↑ : increasing f} (k : ℕ)
                      → f k + ι k ≤ limit f {f↑}
add-finite-part-lemma f {f↑} k =
 ≤-trans (add-finite-part-lemma' f {f↑} k k) (≤-cocone-simple f)

limit-reach-next-ω : (f : ℕ → Brw){f↑ : increasing f}
                   → (k n : ℕ)
                   → (ω · ι k) ≤ f n
                   → ω · ι (suc k) ≤ limit f {f↑}
limit-reach-next-ω f {f↑} k n p = simulation→≤ (λ m → (n N+ m , q m))
 where
  q : (m : ℕ)  → (ω · ι k + ι m) ≤ f (n N+ m)
  q k = ≤-trans (+x-mono (ι k) p) (add-finite-part-lemma' f {f↑} n k)

limit-reach-next-ω' : (α : Brw)
                    → is-lim α
                    → (k : ℕ)
                    → (ω · ι k) < α
                    → ω · ι (suc k) ≤ α
limit-reach-next-ω' α α-lim k l =
 reduce-to-canonical-limits (λ x → (ω · ι k) < x → ω · ι (suc k) ≤ x)
                            (λ x → isProp→ isProp⟨≤⟩)
                            [2]
                            α α-lim l
  where
   [1] : (f : ℕ → Brw) (f↑ : increasing f)
       → Σ[ n ∈ ℕ ] ω · ι k < f n → ω · ι (suc k) ≤ limit f
   [1] f f↑ (n , l) = limit-reach-next-ω f k n (<-in-≤ l)
   [2] : (f : ℕ → Brw) (f↑ : increasing f) → (ω · ι k) < limit f → ω · ι (suc k) ≤ limit f
   [2] f f↑ l = ∥-∥rec isProp⟨≤⟩ ([1] f f↑) (below-limit-lemma (ω · ι k) f l)


cancel-finite-limit-≤-left : (f g : ℕ → Brw) {f↑ : increasing f} {g↑ : increasing g} (k : ℕ)
                    → limit f {f↑} < limit g {g↑}
                    → limit f{f↑} + ι k ≤ limit g {g↑}
cancel-finite-limit-≤-left f g {f↑} {g↑} zero p = <-in-≤ p
cancel-finite-limit-≤-left f g {f↑} {g↑} (suc zero) p = p
cancel-finite-limit-≤-left f g {f↑} {g↑} (suc (suc k)) p = x<lim→sx<lim g (limit f + ι k)
                                                         (cancel-finite-limit-≤-left f g (suc k) p)

cancel-finite-lim-≤-left : (α β : Brw) → is-lim α → is-lim β
                       → (k : ℕ) → α < β → α + ι k ≤ β
cancel-finite-lim-≤-left α β α-lim = h α α-lim β
 where
  h : (α : Brw) → is-lim α → (β : Brw) → is-lim β
    → (k : ℕ) → α < β → α + ι k ≤ β
  h = reduce-to-canonical-limits _
       (λ _ → isPropΠ4 (λ _ _ _ _ → ≤-trunc))
       [1]
   where
    [1] : (f : ℕ → Brw) (f↑ : increasing f) (β : Brw)
        → is-lim β → (k : ℕ) → limit f < β → (limit f + ι k) ≤ β
    [1] f f↑ = reduce-to-canonical-limits _
                (λ _ → isPropΠ2 (λ _ _ → ≤-trunc))
                (λ g g↑ → cancel-finite-limit-≤-left f g)

cancel-finite-limit-≤ : (f : ℕ → Brw) {f↑ : increasing f} (x : Brw) (k : ℕ)
                      → limit f {f↑} ≤ x + ι k
                      → limit f {f↑} ≤ x
cancel-finite-limit-≤ f {f↑} x zero u = u
cancel-finite-limit-≤ f {f↑} x (suc k) u = cancel-finite-limit-≤ f {f↑} x k (lim≤sx→lim≤x f (x + ι k) u)

cancel-finite-limit-≤-↔ : (f : ℕ → Brw) {f↑ : increasing f} (x : Brw) (k : ℕ)
                        → limit f {f↑} ≤ x + ι k
                        ↔ limit f {f↑} ≤ x
cancel-finite-limit-≤-↔ f x k =
 cancel-finite-limit-≤ f x k ,
 (λ l → ≤-trans l (x+-mono (ι-mono {m = k} N.zero-≤)))

cancel-finite-lim-≤ : (α β : Brw) (αlim : is-lim α) (k : ℕ)
                     → α ≤ β + ι k → α ≤ β
cancel-finite-lim-≤ α β αlim k u = ∥-∥rec ≤-trunc [1] αlim
 where
  [1] : is-Σlim α → α ≤ β
  [1] ((f , f↑) , p) = subst (λ - → - ≤ β) (sym σ) [3]
   where
      σ : α ≡ limit f {f↑}
      σ = is-lim→≡limit p
      [3] : limit f ≤ β
      [3] = cancel-finite-limit-≤ f β k (subst2 (λ x y → x ≤ y + ι k) σ refl u)

finite-right-cancellation : (α β : Brw) (αlim : is-lim α) (k : ℕ)
                               → α + ι k ≤ β + ι k → α ≤ β
finite-right-cancellation α β αlim k p = cancel-finite-lim-≤ α β αlim k (≤-trans (x+-increasing (ι k)) p)

≤-offset-by-ι : (f : ℕ → Brw) {f↑ : increasing f} (x : Brw) {n k : ℕ}
              → x ≤ f n
              → x + ι k ≤ f (n N+ k)
≤-offset-by-ι f {f↑} x {n} {zero} l = subst (λ - → x ≤ f -) (sym (+-zero n)) l
≤-offset-by-ι f {f↑} x {n} {suc k} l = [3]
 where
  [1] : x + ι k ≤ f (n N+ k)
  [1] = ≤-offset-by-ι f {f↑} x l
  [2] : succ (x + ι k) ≤ f (suc (n N+ k))
  [2] = ≤-trans (≤-succ-mono [1]) (f↑ (n N+ k))
  [3] : succ (x + ι k) ≤ f (n N+ suc k)
  [3] = subst (λ - → succ (x + ι k) ≤ -) (cong f (sym (+-suc n k))) [2]



·-assoc : ∀ {a b} c → a · (b · c) ≡ (a · b) · c
·-assoc {a} {b} =
  Brw-ind (λ c → a · (b · c) ≡ (a · b) · c)
          (λ c → Brw-is-set _ _)
          refl
          (λ {a'} ih → sym (·-+-distributivity {a} {b · a'} b) ∙ cong (λ z → z + a · b) ih)
          limitCase
 where
  limitCase : ∀ {f} {f↑} → (∀ k → a · b · f k ≡ (a · b) · f k) →
                a · b · limit f ≡ (a · b) · limit f {f↑}
  limitCase {f} {f↑} ih with decZero b | decZero (a · b)
  limitCase {f} {f↑} ih | yes b≡zero | yes ab≡zero = refl
  limitCase {f} {f↑} ih | yes b≡zero | no  ab≢zero =
      ⊥.rec (ab≢zero (subst (λ z → a · z ≡ zero) (sym b≡zero) refl))
  limitCase {f} {f↑} ih | no  b≢zero | yes ab≡zero with decZero a
  limitCase {f} {f↑} ih | no  b≢zero | yes ab≡zero | yes a≡zero = refl
  limitCase {f} {f↑} ih | no  b≢zero | yes ab≡zero | no  a≢zero =
      ⊥.rec (·-no-zero-divisors a≢zero b≢zero ab≡zero)
  limitCase {f} {f↑} ih | no  b≢zero | no  ab≢zero with decZero a
  limitCase {f} {f↑} ih | no  b≢zero | no  ab≢zero | yes a≡zero =
      ⊥.rec (ab≢zero (subst (λ z → z · b ≡ zero) (sym a≡zero) (zero·y≡zero b)))
  limitCase {f} {f↑} ih | no  b≢zero | no  ab≢zero | no  a≢zero =
      bisim (λ n → a · b · f n) (λ n → (a · b) · f n)
            ((λ k → ∣ k , ≤-refl-≡ (ih k) ∣) , λ k → ∣ k , ≤-refl-≡ (sym (ih k)) ∣)

exp-homomorphism : ∀ {a b c} → a ^ (b + c) ≡ a ^ b · a ^ c
exp-homomorphism {a} {b} {c} =
  Brw-ind (λ c → a ^ (b + c) ≡ a ^ b · a ^ c)
          (λ c → Brw-is-set _ _)
          (sym (zero+y≡y (a ^ b)))
          (λ {a'} ih → cong (_· a) ih ∙ sym (·-assoc {a ^ b} {a ^ a'} a))
          limitCase
          c
 where
  limitCase : ∀ {f} {f↑} → (∀ k → a ^ (b + f k) ≡ a ^ b · a ^ f k) →
                a ^ (b + limit f {f↑}) ≡ a ^ b · a ^ limit f {f↑}
  limitCase {f} {f↑} ih with decZeroOneMany a
  limitCase {f} {f↑} ih | inl a≡zero = refl
  limitCase {f} {f↑} ih | inr (inl a≡one) = sym (zero+y≡y (a ^ b) ∙ cong (_^ b) a≡one ∙ one^y≡one b)
  limitCase {f} {f↑} ih | inr (inr one<a) with decZero (a ^ b)
  limitCase {f} {f↑} ih | inr (inr one<a) | yes a^b≡zero =
      ⊥.rec (zero≢a^ b (one<x→x≢zero one<a) (sym a^b≡zero))
  limitCase {f} {f↑} ih | inr (inr one<a) | no  a^b≢zero =
      bisim (λ n → a ^ (b + f n)) (λ n → a ^ b · a ^ f n)
            ((λ k → ∣ k , ≤-refl-≡ (ih k) ∣) , λ k → ∣ k , ≤-refl-≡ (sym (ih k)) ∣)

y·one≡y : (y : Brw) → y · one ≡ y
y·one≡y y = zero+y≡y y

one·y≡y : (y : Brw) → one · y ≡ y
one·y≡y =
  Brw-ind (λ y → one · y ≡ y)
          (λ y → Brw-is-set _ _)
          refl
          (cong succ)
          (λ {f} {f↑} ih → bisim (λ n → one · f n) f
                                 ((λ k → ∣ k , ≤-refl-≡ (ih k) ∣) ,
                                  (λ k → ∣ k , ≤-refl-≡ (sym (ih k)) ∣)))

x·2=x+x : (x : Brw) → x · ι 2 ≡ x + x
x·2=x+x x = cong (_+ x) (zero+y≡y x)

x·3=x+x+x : (x : Brw) → x · ι 3 ≡ (x + x) + x
x·3=x+x+x x = cong (λ - → (- + x) + x ) (zero+y≡y x)

x·n=1=x+xn : {n : ℕ} → (x : Brw) → x · ι n + x ≡ x + x · ι n
x·n=1=x+xn {zero} x = zero+y≡y x
x·n=1=x+xn {suc n} x = cong (_+ x) (x·n=1=x+xn {n} x) ∙ sym (+-assoc x)

nonzero·limit-is-lim : {x : Brw} {f : ℕ → Brw} {f↑ : increasing f}
                     → (x ≤ zero → ⊥)
                     → is-lim (x · limit f {f↑})
nonzero·limit-is-lim {x} {f} {f↑} x-non-zero with decZero x
... | yes p = ⊥.elim (x-non-zero (≤-refl-≡ p))
... | no  q = is-lim-limit (λ n → x · f n) (x·-increasing q f↑)


ω=ω^1 : ω ≡ ω^ one
ω=ω^1 = bisim ι (λ n → one · ι n)
              ((λ k → ∣ k , ≤-refl-≡ (sym (one·y≡y (ι k))) ∣) ,
               (λ k → ∣ k , ≤-refl-≡ (one·y≡y (ι k)) ∣))

ω-absorbs-finite : ∀ n → ι (suc n) · ω ≡ ω
ω-absorbs-finite zero =
  bisim (λ n → succ zero · ι n) ι
        ((λ k → ∣ k , ≤-refl-≡ (one·y≡y (ι k)) ∣) ,
         (λ k → ∣ k , ≤-refl-≡ (sym (one·y≡y (ι k))) ∣))
ω-absorbs-finite (suc n) =
  bisim (λ k → succ (succ (ι n)) · ι k) (λ k → succ (ι n) · ι k)
        ((λ k → ∣ k N+ k , subst (λ z → fst z ≤ snd z)
                                 (λ i → (cong ι (·-comm (suc (suc n)) k) ∙
                                         ι-·-commutes (suc (suc n)) k) i ,
                                        (cong ι (·-comm (suc n) (k N+ k)) ∙
                                         ι-·-commutes (suc n) (k N+ k)) i)
                                 (increasing→monotone ι-increasing (n+2·k≤⟨n+1⟩·2k n k)) ∣) ,
         (λ k → ∣ k , ·x-mono (ι k) ≤-succ-incr-simple ∣))
  ∙ ω-absorbs-finite n
 where
  n+2·k≤⟨n+1⟩·2k : ∀ n k → (suc (suc n)) N· k N.≤ (suc n) N· (k N+ k)
  n+2·k≤⟨n+1⟩·2k n k = subst (λ z → z N.≤ (suc n) N· (k N+ k))
                             (sym (N+-assoc k k (n N· k)))
                             (N.≤-k+ {k = k N+ k} (N≤-k· {k = n} (N.≤-+k {k = k} N.zero-≤)))

ω^x-absorbs-finite : ∀ {x n} → zero < x → ι (suc n) · ω^ x ≡ ω^ x
ω^x-absorbs-finite {x} {n} =
  Brw-ind (λ x → zero < x → ι (suc n) · ω^ x ≡ ω^ x)
          (λ x → isProp→ (Brw-is-set _ _))
          (λ zero<zero → ⊥.rec (<-irreflexive _ zero<zero))
          sucCase
          (λ {f} {f↑} ih _ →
             limit-skip-first (λ k → succ (ι n) · ω ^ f k)
           ∙ bisim (λ k → succ (ι n) · ω ^ f (suc k)) (λ k → ω ^ f k)
                   ((λ k → ∣ suc k , ≤-refl-≡ (ih (suc k) (increasing→zero<fsuc f↑)) ∣) ,
                    (λ k → ∣ k , ≤-trans (ω^-mono (<-in-≤ (f↑ k)))
                                         (≤-refl-≡ (sym (ih (suc k)(increasing→zero<fsuc f↑)))) ∣)))
          x
 where
  sucCase : ∀ {x'} → (zero < x' → ι (suc n) · ω^ x' ≡ ω^ x') →
              zero < succ x' → ι (suc n) · ω^ (succ x') ≡ ω^ (succ x')
  sucCase {x'} ih zero<sx' with decZero x'
  ... | yes x'≡zero = subst (λ z → ι (suc n) · z ≡ z)
                            (ω=ω^1 ∙ cong (λ z → ω^ (succ z)) (sym x'≡zero))
                            (ω-absorbs-finite n)
  ... | no  x'≢zero = ·-assoc {ι (suc n)} {ω^ x'} ω
                    ∙ cong (_· ω) (ih (zero≠x→zero<x _ (λ zero≡x → x'≢zero (sym zero≡x))))


{- Lemmas about ω^ c -}

ω^-mono-< : {x y : Brw} → x < y → ω^ x < ω^ y
ω^-mono-< {x} {y} x<y with decZero (ω^ x)
... | yes ω^x≡zero = ⊥.rec (zero≢a^ x (λ ω≡zero → zero≠lim (sym ω≡zero)) (sym ω^x≡zero) )
... | no ω^x≢zero = ≤-trans (ω^-preserves-increasing {succ-from x} succ-from-increasing zero)
                            (ω^-mono x<y)

zero<ω^c : (c : Brw) → zero < ω^ c
zero<ω^c c = zero≠x→zero<x _ (zero≢a^ c λ ω≡zero → zero≠lim (sym ω≡zero))

a<omega^a : {a : Brw} → a ≤ ω^ a
a<omega^a {a} =
  Brw-ind (λ a → a ≤ ω^ a)
          (λ a → ≤-trunc)
          ≤-zero
          (λ {a} ih → ≤-trans (≤-succ-mono ih) (ω^-mono-< (<-succ-incr-simple {a})))
          (λ {f} {f↑} ih → weakly-bisimilar→lim≤lim f _ λ k → ∣ k , ih k ∣)
          a

ω^one≡ω : ω^ one ≡ ω
ω^one≡ω = bisim _ _ ((λ k → ∣ k , ≤-refl-≡ (one·y≡y _) ∣) ,
                     (λ k → ∣ k , ≤-refl-≡ (sym (one·y≡y _)) ∣))

zero<ω : zero < ω
zero<ω = <∘≤-in-< (zero<ω^c one) (≤-refl-≡ ω^one≡ω)

ω<ω+ω : ω < ω + ω
ω<ω+ω = x+-mono-< {ω} {zero} {ω} zero<ω

ω² ω³ : Brw
ω² = ω · ω
ω³ = ω² · ω

ω·x-islim : (x : Brw) → is-lim (ω · x) ⊎ (x ≡ zero)
ω·x-islim = Brw-ind P P-is-prop P₀ (λ {x} → Pₛ {x}) (λ {f} {f↑} → Pₗ {f} {f↑})
 where
  P : (x : Brw) → Type
  P x = is-lim (ω · x) ⊎ (x ≡ zero)

  P-is-prop : (x : Brw) → isProp (P x)
  P-is-prop x = isProp⊎ isProp⟨is-lim⟩ (Brw-is-set x zero) [1]
   where
    [1] : is-lim (ω · x) → x ≡ zero → ⊥
    [1] l z = unique.not-z-and-l (ω · x) (≡zero→is-zero (cong (ω ·_) z)) l

  P₀ : P zero
  P₀ = inr refl

  Pₛ : {x : Brw} → P x → P (succ x)
  Pₛ {x} _ = inl (is-lim-limit (λ n → ω · x + ι n) (λ n → x+-mono (ι-increasing n)))

  Pₗ : {f : ℕ → Brw} {f↑ : increasing f} → ((k : ℕ) → P (f k)) → P (limit f {f↑})
  Pₗ {f} {f↑} _ = inl (is-lim-limit (λ n → ω · f n) (x·-increasing (λ p → zero≠lim (sym p)) f↑))

ω·sk-islim : (k : ℕ) → is-lim (ω · (ι (suc k)))
ω·sk-islim k = [1] (ω·x-islim (ι (suc k)))
 where
  [1] : is-lim (ω · ι (suc k)) ⊎ (ι (suc k) ≡ zero) → is-lim (ω · (ι (suc k)))
  [1] (inl l) = l
  [1] (inr e) = ⊥.rec (zero≠succ (sym e))

  f : ℕ → Brw
  f n = ω · ι k + ι n
  f↑ : is-<-increasing f
  f↑ n = x+-mono (ι-increasing n)

ω·k-islim' : (k : ℕ) → (k>0 : zero < ι k) → is-lim (ω · ι k)
ω·k-islim' zero = λ z → ⊥.rec (≮-zero (λ b → ≤-zero) zero z)
ω·k-islim' (suc k) p = ∣ (f , f↑) , limit-is-sup f f↑ ∣
 where
  f : ℕ → Brw
  f n = ω · ι k + ι n
  f↑ : is-<-increasing f
  f↑ n = x+-mono (ι-increasing n)

ω^k-is-lim : (k : ℕ) → is-lim (ω ^ (succ (ι k)))
ω^k-is-lim zero = is-lim-limit (λ n → succ zero · ι n) _
ω^k-is-lim (suc k) = nonzero·limit-is-lim (is-lim≰zero (ω^k-is-lim k))

ω·n>ω→n>0 : (n k : ℕ) → (ω < ω · ι n + ι k → ℕ.zero N.< n)
ω·n>ω→n>0 zero k h = ⊥.elim (<-irreflexive ω [3])
 where
  [1] : ι k < ω
  [1] = ≤-cocone ι (ι-increasing k)
  [2] : ω < ι k
  [2] = subst (ω <_) (zero+y≡y (ι k)) h
  [3] : ω < ω
  [3] = <-trans ω (ι k) ω [2] [1]
ω·n>ω→n>0 (suc n) k _ = N.suc-≤-suc N.zero-≤

ω·n<ω·n+1 : (n : ℕ) → (ω · ι n < ω · ι (suc n))
ω·n<ω·n+1 n = x·-mono-< [1] (ι-increasing n)
 where
  [1] : ω ≡ zero → ⊥
  [1] ν = zero≠lim (sym ν)

ω·0+n=n : (n : ℕ) → ι n ≡ ω · ι 0 + ι n
ω·0+n=n n = sym (zero+y≡y (ι n))

ω·n≤ω·m+k→ω·n≤ω·m : (n m k : ℕ) → ω · ι n ≤ ω · ι m + ι k  → ω · ι n ≤ ω · ι m
ω·n≤ω·m+k→ω·n≤ω·m zero m k p = ≤-zero
ω·n≤ω·m+k→ω·n≤ω·m (suc n) zero k p =
 ⊥.elim {_} {λ _ → ω · ι (suc n) ≤ zero} (lim≰ι [1])
  where
   [1] : ω · ι (suc n) ≤ ι k
   [1] = subst (ω · ι (suc n) ≤_) (zero+y≡y (ι k)) p
ω·n≤ω·m+k→ω·n≤ω·m (suc n) (suc m) =
 cancel-finite-lim-≤
  (ω · ι (suc n))
  (ω · ι (suc m))
  (ω·sk-islim n)


ω·1≡ω : ω · ι 1 ≡ ω
ω·1≡ω = y·one≡y ω

ω+ω≡ω·2 : ω + ω ≡ ω · ι 2
ω+ω≡ω·2 = sym (x·2=x+x ω)

ω+ω-islim : is-lim (ω + ω)
ω+ω-islim = subst (λ z → is-lim z) (sym ω+ω≡ω·2) (ω·sk-islim 1)

ω^ι2≡ω² : ω ^ (ι 2) ≡ ω²
ω^ι2≡ω² = limit-pointwise-equal _ _
            (λ n → cong (_· ι n) (limit-pointwise-equal _ _
                                   (λ k → one·y≡y (ι k))))

ω^ι3≡ω³ : ω ^ (ι 3) ≡ ω³
ω^ι3≡ω³ = cong (_· ω) ω^ι2≡ω²

ω·k-split : (k n m : ℕ) → (k ≡ n N+ m) → ω · ι k ≡ ω · ι n + ω · ι m
ω·k-split k n m p =   cong (λ z → ω · z) (cong (λ u → ι u) p ∙ ι-+-commutes' n m)
                    ∙ sym (·-+-distributivity (ι m))

limit-cancel-+ω-≤ : (x : Brw) (f : ℕ → Brw) {f↑ : increasing f}
             → limit f {f↑} + ω ≤ x + ω
             → limit f {f↑} ≤ x
limit-cancel-+ω-≤ x f {f↑} l = ∥-∥rec isProp⟨≤⟩ (uncurry [2]) [1]
 where
  [1] : ∥ Σ[ m ∈ ℕ ] limit f ≤ x + ι m ∥
  [1] = lim≤lim→weakly-bisimilar (λ n → limit f + ι n) (λ n → x + ι n) l 0

  [2] : (m : ℕ) → limit f {f↑} ≤ x + ι m → limit f {f↑} ≤ x
  [2] zero l = l
  [2] (suc m) l = [2] m (lim≤sx→lim≤x f (x + ι m) l)

lim-cancel-+ω-≤ : (x y : Brw) → is-lim y → y + ω ≤ x + ω → y ≤ x
lim-cancel-+ω-≤ x y lim = ∥-∥rec (isPropΠ (λ _ → isProp⟨≤⟩)) [1] lim
 where
  [1] : is-Σlim y → y + ω ≤ x + ω → y ≤ x
  [1] ((f , f↑) , p) = subst (λ - → - + ω ≤ x + ω → - ≤ x) (sym [2]) [3]
   where
    [2] : y ≡ limit f {f↑}
    [2] = is-lim→≡limit p
    [3] : (limit f + ω) ≤ (x + ω) → limit f ≤ x
    [3] = limit-cancel-+ω-≤ x f {f↑}

ω·ssk≮ω : (k : ℕ) → ω · ι (suc k) + ω ≤ ω → ⊥
ω·ssk≮ω k p = lim≰zero (lim-cancel-+ω-≤ zero (ω · ι (suc k)) (ω·sk-islim k) p')
 where
  p' = subst (λ z →  ω · ι (suc k) + ω ≤ z) (sym ω·1≡ω) p

ω·2≮ω : ω + ω ≤ ω → ⊥
ω·2≮ω p = ω·ssk≮ω 0 (subst (λ z → z + ω ≤ ω) (sym ω·1≡ω) (p))

ω·-cancel-≤ : (x y : Brw) → ω · x ≤ ω · y → x ≤ y
ω·-cancel-≤ = Brw-ind _ i P₀ Pₛ Pₗ
 where
  i : (x : Brw) → isProp ((y : Brw) → (ω · x) ≤ (ω · y) → x ≤ y)
  i x = isPropΠ2 (λ y l → ≤-trunc)
  P₀ : (y : Brw) → (ω · zero) ≤ (ω · y) → zero ≤ y
  P₀ y l = ≤-zero
  Pₛ : {x : Brw}
       → ((y : Brw) → (ω · x) ≤ (ω · y) → x ≤ y)
       → (y : Brw) → ω · x + ω ≤ (ω · y) → succ x ≤ y
  Pₛ {x} IH = Brw-ind _ i' Q₀ Qₛ Qₗ
   where
    i' : (y : Brw)
       → isProp (ω · x + ω ≤ (ω · y) → succ x ≤ y)
    i' y = isPropΠ (λ _ → ≤-trunc)
    Q₀ : ω · x + ω ≤ zero → succ x ≤ zero
    Q₀ l = ⊥.elim (lim≰zero l)
    Qₛ : {y : Brw}
       → (ω · x + ω ≤ (ω · y) → succ x ≤ y)
       → ω · x + ω ≤ ω · y + ω
       → succ x ≤ succ y
    Qₛ {y} IH' l with ω·x-islim x
    Qₛ {y} IH' l | inl ω·x-lim with ω·x-islim y
    Qₛ {y} IH' l | inl ω·x-lim | inl ω·y-lim = ≤-succ-mono (IH y [1])
     where
      [1] : ω · x ≤ ω · y
      [1] = ∥-∥rec ≤-trunc [1]' [2]
       where
        [1]' : Σ[ n ∈ ℕ ] (ω · x) ≤ (ω · y + ι n) → (ω · x) ≤ (ω · y)
        [1]' (m , l') = cancel-finite-lim-≤ (ω · x) (ω · y) ω·x-lim  m l'

        [2] : ∥ Σ[ n ∈ ℕ ] (ω · x) ≤ (ω · y + ι n) ∥
        [2] = (lim≤lim→weakly-bisimilar _ _ l 0)
    Qₛ {y} IH' l | inl ω·x-lim | inr y≡zero = ⊥.rec (<-irreflexive (ω · x) [5])
     where
      [1] : (n : ℕ) → ω · y + ι n ≡ ι n
      [1] n = cong (λ - → ω · - + ι n) y≡zero  ∙ zero+y≡y (ι n)
      [2] : ∥ Σ[ n ∈  ℕ ] (ω · x ≤ (ω · y + ι n)) ∥
      [2] = lim≤lim→weakly-bisimilar _ _ l 0
      [3] : ∥ Σ[ n ∈  ℕ ] (ω · x) ≤ ι n ∥
      [3] = ∥-∥map (λ (n , p) → (n , subst ((ω · x) ≤_) ([1] n) p)) [2]
      [4] : (n : ℕ) → ι n < ω · x
      [4] n = ∥-∥rec isProp⟨<⟩ ([4]' n) ω·x-lim
       where
        [4]' : (n : ℕ) → Σ[ f ∈ IncrSeq ] ω · x is-lim-of f
             → ι n < ω · x
        [4]' n ((f , f↑) , p) =
         subst (ι n <_) (sym (is-lim→≡limit {f↑ = f↑} p)) (ι n <lim)
      [5] : (ω · x) < (ω · x)
      [5] = ∥-∥rec isProp⟨<⟩ [5]' [3]
       where
        [5]' : Σ[ n ∈  ℕ ] (ω · x) ≤ ι n → (ω · x) < (ω · x)
        [5]' (n , p) = ≤∘<-in-< p ([4] n)
    Qₛ {y} IH' l | inr x≡zero = ≤-succ-mono (subst (_≤ y) (sym x≡zero) ≤-zero)

    Qₗ : {g : ℕ → Brw} {g↑ : increasing g} →
         ((k : ℕ) → (ω · x + ω) ≤ (ω · g k) → succ x ≤ g k) →
         (ω · x + ω) ≤ (ω · limit g {g↑}) → succ x ≤ limit g {g↑}
    Qₗ {g} {g↑} IH' l = ∥-∥rec ≤-trunc [1] [2]
     where
      [1] : Σ[ n ∈ ℕ ] (ω · x) ≤ (ω · g n) → succ x ≤ limit g
      [1] (m , l') = ≤∘<-in-< (IH (g m) l') (<-cocone-simple g)

      [2] : ∥ Σ ℕ (λ n → (ω · x) ≤ (ω · g n)) ∥
      [2] = lim≤lim→weakly-bisimilar _ _ l 0
  Pₗ : {f : ℕ → Brw} {f↑ : increasing f} →
      ((k : ℕ) (y : Brw) → (ω · f k) ≤ (ω · y) → f k ≤ y) →
      (y : Brw) → limit (λ n → ω · f n) ≤ (ω · y) → limit f ≤ y

  Pₗ {f} {f↑} IH = Brw-ind _ i' Q₀ Qₛ (λ {g} {g↑} → Qₗ {g} {g↑})
   where
    i' : (y : Brw)
       → isProp (limit (λ n → ω · f n) ≤ (ω · y) → limit f {f↑} ≤ y)
    i' y = isPropΠ (λ _ → ≤-trunc)

    Q₀ : limit (λ n → ω · f n) ≤ zero → limit f ≤ zero
    Q₀ l = ⊥.rec (lim≰zero (subst (limit (λ n → ω · f n) {f↑ = g↑} ≤_)
                                  (x≤zero→x≡zero l)
                                  ≤-refl))
     where
      g↑ = x·-increasing (λ x≡zero → subst (λ z → isZero z → ⊥) x≡zero (λ ()) tt) f↑

    Qₛ : {y : Brw}
       → (limit (λ n → ω · f n) ≤ (ω · y) → limit f ≤ y)
       → limit (λ n → ω · f n) ≤ limit (λ n → ω · y + ι n)
       → limit f ≤ succ y
    Qₛ {y} IH' l with ω·x-islim y
    Qₛ {y} IH' l | inl ω·y-islim = ≤-limiting f [2]
     where
      [1] : (k : ℕ) → Σ ℕ (λ n → (limit ι · f k) ≤ (limit ι · y + ι n)) → f k ≤ succ y
      [1] k (m , l') with ω·x-islim (f k)
      [1] k (m , l') | inl ω·fk-islim =
       ≤-trans (IH k y (cancel-finite-lim-≤ (ω · f k) (ω · y)
                                             ω·fk-islim m l'))
               ≤-succ-incr-simple
      [1] k (m , l') | inr fk≡zero = subst (_≤ succ y) (sym fk≡zero) ≤-zero
      [2] : (k : ℕ) → f k ≤ succ y
      [2] k = ∥-∥rec ≤-trunc ([1] k) (lim≤lim→weakly-bisimilar _ _ l k)
    Qₛ {y} IH' l | inr y≡zero = ⊥.rec (<-irreflexive (ω · f 1) [6])
     where
      [1] : (n : ℕ) → ω · y + ι n ≡ ι n
      [1] n = cong (λ - → ω · - + ι n) y≡zero  ∙ zero+y≡y (ι n)
      [2] : ∥ Σ[ n ∈  ℕ ] (ω · f 1) ≤ (ω · y + ι n) ∥
      [2] = lim≤lim→weakly-bisimilar _ _ l 1
      [3] : ∥ Σ[ n ∈  ℕ ] (ω · f 1) ≤ ι n ∥
      [3] = ∥-∥map (λ (n , p) → (n , subst ((ω · f 1) ≤_) ([1] n) p)) [2]
      [4] : is-lim (ω · f 1)
      [4] with ω·x-islim (f 1)
      ... | inl ω·f1-islim = ω·f1-islim
      ... | inr f1≡zero = ⊥.rec (succ≰zero (subst (succ (f 0) ≤_) f1≡zero (f↑ 0)))
      [5] : (n : ℕ) → ι n < ω · f 1
      [5] n = ∥-∥rec isProp⟨<⟩ ([5]' n) [4]
       where
        [5]' : (n : ℕ) → Σ[ g ∈ IncrSeq ] ω · (f 1) is-lim-of g
             → ι n < ω · f 1
        [5]' n ((g , g↑) , p) =
         subst (ι n <_) (sym (is-lim→≡limit {f↑ = g↑} p)) (ι n <lim)
      [6] : ω · f 1 < ω · f 1
      [6] = ∥-∥rec isProp⟨<⟩ [6]' [3]
       where
        [6]' : Σ[ n ∈  ℕ ] (ω · f 1) ≤ ι n → (ω · f 1) < (ω · f 1)
        [6]' (n , p) = ≤∘<-in-< p ([5] n)

    Qₗ : {g : ℕ → Brw} {g↑ : increasing g} →
      ((k : ℕ) → limit (λ n → ω · f n) ≤ (ω · g k) → limit f ≤ g k) →
      limit (λ n → ω · f n) ≤ (ω · limit g {g↑}) → limit f ≤ limit g
    Qₗ {g} {g↑} IH' l = weakly-bisimilar→lim≤lim _ _ [2]
     where
      [1] : (n : ℕ) → Σ[ k ∈ ℕ ] (ω · f n) ≤ (ω · g k) → Σ[ k ∈ ℕ ] f n ≤ g k
      [1] n (k , l') = (k , IH n (g k) l')

      [2] : f ≲ g
      [2] n = ∥-∥map ([1] n) (lim≤lim→weakly-bisimilar _ _ l n)

+ω-absorbs-finite : (n : ℕ) → ι n + ω ≡ ω
+ω-absorbs-finite n =
 ≤-antisym (≤-limiting
             (λ m → ι n + ι m)
             (λ m → ι n + ι m  ≤⟨ ≤-refl-≡ (sym (ι-+-commutes' n m)) ⟩
                    ι (n N+ m) ≤⟨ ≤-cocone-simple ι ⟩
                    ω          ≤∎))
           (≤-limiting ι
            (λ k → ι k                     ≤⟨ x+-increasing (ι n) ⟩
                   ι k + ι n               ≤⟨ l₁ k ⟩
                   ι n + ι k               ≤⟨ l₂ k ⟩
                   limit (λ m → ι n + ι m) ≤∎))
 where
  l₁ : (k : ℕ) → ι k + ι n ≤ ι n + ι k
  l₁ k = ≤-refl-≡ (sym (ι-+-commutes k n) ∙ ι-+-commutes' n k)
  l₂ : (k : ℕ) → ι n + ι k ≤ limit (λ m → ι n + ι m)
  l₂ k = ≤-cocone-simple (λ m → ι n + ι m) {_} {k}

ω-finite-power-comm : (n : ℕ) → ω ^ ι n · ω ≡ ω · ω ^ ι n
ω-finite-power-comm zero =
 limit-pointwise-equal _ _ λ n → one·y≡y (ι n) ∙ sym (zero+y≡y (ι n))
ω-finite-power-comm (suc n) =
 cong (_· ω) (ω-finite-power-comm n) ∙ sym (·-assoc {ω} {ω ^ ι n} ω)

ωⁿ≤right-summand : {n k : ℕ} {x y : Brw}
                 → ω ^ (succ (ι n)) ≤ x + y
                 → x < ω ^ (ι n) · ι k
                 → ω ^ (succ (ι n)) ≤ y
ωⁿ≤right-summand {n} {k} {x} {_} = Brw-ind P (λ y → isPropΠ2 (λ _ _ → ≤-trunc)) P₀ Pₛ Pₗ _
 where
  N = succ (ι n)
  P : Brw → Type
  P y = ω ^ N ≤ x + y
      → x < ω ^ (ι n) · ι k
      → ω ^ N ≤ y
  P₀ : P zero
  P₀ l₁ l₂ = ⊥.elim (<-irreflexive (ω ^ N) [4])
   where
    _ : ω ^ N ≡ ω ^ (ι n) · ω
    _ = refl
    [1] : ω ^ N ≤ x
    [1] = l₁
    [2] : x < ω ^ (ι n) · ι k
    [2] = l₂
    [3] : ω ^ (ι n) · ι k ≤ ω ^ N
    [3] = x·-mono (≤-cocone-simple ι {ι-increasing} {k})
    [4] : ω ^ N < ω ^ N
    [4] = ≤∘<-in-< [1] (<∘≤-in-< [2] [3])
  Pₛ : {y : Brw} → P y → P (succ y)
  Pₛ {y} IH l₁ l₂ = ≤-trans [3] ≤-succ-incr-simple
   where
    [1] : ω ^ N ≤ succ (x + y)
    [1] = l₁
    [2] : ω ^ N ≤ x + y
    [2] = is-lim-cancel-succ-≤ (ω ^ N) (x + y) (ω^k-is-lim n) [1]
    [3] : ω ^ N ≤ y
    [3] = IH [2] l₂
  Pₗ : {f : ℕ → Brw} {f↑ : increasing f}
     → ((i : ℕ) → P (f i))
     → P (limit f {f↑})
  Pₗ {f} {f↑} IH l₁ l₂ with decZero (ω ^ ι n)
  ... | yes ω^n-is-zero = ≤-zero
  ... | no  ω^n-is-non-zero = weakly-bisimilar→lim≤lim _ _ [4]
   where
    [1] : (m : ℕ)
        → Σ[ v ∈ ℕ ] (ω ^ ι n · ι (k N+ m) ≤ x + f v)
        → Σ[ v ∈ ℕ ] (ω ^ ι n · ι (k N+ m) ≤ ω ^ ι n · ι k + f v)
    [1] m (v , l₃) = v , ≤-trans l₃ (+x-mono (f v) (<-in-≤ l₂))
    [2] : (m : ℕ) → ∥ Σ[ v ∈ ℕ ] (ω ^ ι n · ι (k N+ m) ≤ ω ^ ι n · ι k + f v) ∥
    [2] m = ∥-∥map ([1] m) (lim≤lim→weakly-bisimilar (λ j → ω ^ ι n · ι j) (λ i → x + f i) l₁ (k N+ m))
    [3] : (m : ℕ) → ∥ Σ[ v ∈ ℕ ] (ω ^ ι n · ι k + ω ^ ι n · ι m ≤ ω ^ ι n · ι k + f v) ∥
    [3] m = subst (λ - → ∥ Σ[ v ∈ ℕ ] (- ≤ ω ^ ι n · ι k + f v) ∥) ([3]₂ ∙ [3]₁) ([2] m)
     where
      [3]₁ : ω ^ ι n · (ι k + ι m) ≡ ω ^ ι n · ι k + ω ^ ι n · ι m
      [3]₁ = sym (·-+-distributivity {ω ^ ι n} {ι k} (ι m))
      [3]₂ : ω ^ ι n · ι (k N+ m) ≡ ω ^ ι n · (ι k + ι m)
      [3]₂ = cong (ω ^ ι n ·_) (ι-+-commutes' k m)
    [4] : (m : ℕ) → ∥ Σ[ v ∈ ℕ ] (ω ^ ι n · ι m ≤ f v) ∥
    [4] m = ∥-∥map (λ (v , l₃) → (v , +-leftCancel-≤ (ω ^ ι n · ι k) _ _ l₃)) ([3] m)


{- Brouwer ordinals of the form ω^ c are additive principal -}

is-additive-principal : Brw → Type
is-additive-principal x = (a : Brw) → a < x → a + x ≡ x

is-additive-principal-≤ : ∀ {x} → (∀ a → a < x → a + x ≤ x) → is-additive-principal x
is-additive-principal-≤ {x} p a a<x =
  ≤-antisym (p a a<x) (subst (λ z → z ≤ a + x) (zero+y≡y x) (+x-mono x ≤-zero))

additive-principal-ω^ : ∀ (c : Brw) → is-additive-principal (ω^ c)
additive-principal-ω^ =
  Brw-ind (λ c → is-additive-principal (ω^ c))
          (λ c → isPropΠ (λ a → isProp→ (Brw-is-set _ _)))
          (λ a sa≤one → cong succ (x≤zero→x≡zero (≤-succ-mono⁻¹ sa≤one)))
          (λ {c} _ → additive-principal-ω^succ c)
          (λ {f} {f↑} ih → additive-principal-ω^lim f f↑ ih)
 where
  additive-principal-ω^succ : ∀ c → is-additive-principal (ω^ (succ c))
  additive-principal-ω^succ c with decZero (ω^ c)
  ... | yes x = λ a a<zero → ⊥.rec (succ≰zero a<zero)
  ... | no qq =
    is-additive-principal-≤ (λ a a<ω^c·ω →
      weakly-bisimilar→lim≤lim _ _
        (λ k → ∥-∥rec isPropPropTrunc
          (λ (l , a<ω^c·l ) →
            ∣ k N+ l , ≤-trans (+x-mono (ω^ c · ι k) (<-in-≤ a<ω^c·l))
                               (≤-refl-≡ (·-+-distributivity {ω^ c} {ι l} (ι k)
                                        ∙ cong (ω^ c ·_) (sym (ι-+-commutes l k)))) ∣)
        (below-limit-lemma _ _ a<ω^c·ω)))

  additive-principal-ω^lim : ∀ f f↑ → ((k : ℕ) → is-additive-principal (ω^ (f k))) →
                               is-additive-principal (ω^ (limit f {f↑}))
  additive-principal-ω^lim f f↑ ih =
    is-additive-principal-≤ (λ a a<ω^fn →
                               weakly-bisimilar→lim≤lim _ _
                                 (λ k → ∥-∥rec isPropPropTrunc (λ (l , a<ω^fl) → helper k l a<ω^fl)
                                                               (below-limit-lemma _ _ a<ω^fn)))
   where
    helper : ∀ {a} k l (a<ω^fn : a < ω^ (f l)) → ∥ Σ[ n ∈ ℕ ] (a + ω ^ f k) ≤ (ω ^ f n) ∥
    helper {a} k l a<ω^fl with k N.≟ l
    ... | N.lt k<l =
      ∣ l , ≤-trans (x+-mono {a} {ω^ (f k)} {ω^ (f l)}
                            (ω^-mono (increasing→monotone f↑ (N.<-weaken k<l))))
                    (≤-refl-≡ (ih l a a<ω^fl)) ∣
    ... | N.eq k≡l = ∣ l , ≤-refl-≡ (cong (λ z → a + ω^ (f z)) k≡l ∙ ih l a a<ω^fl) ∣
    ... | N.gt l<k =
      ∣ k , ≤-refl-≡ (ih k a (≤-trans a<ω^fl (ω^-mono (increasing→monotone f↑ (N.<-weaken l<k))))) ∣

additive-principal-ω^-closure : ∀ c {a b} → a < ω^ c → b < ω^ c → a + b < ω^ c
additive-principal-ω^-closure c a<ω^c b<ω^c =
  <∘≤-in-< (x+-mono-< b<ω^c) (≤-refl-≡ (additive-principal-ω^ c _ a<ω^c))

{- Definitions of ε₀ and proof that it is a fixed point of ω^ -}

ω↑↑ : ℕ → Brw
ω↑↑  0      = one
ω↑↑ (suc i) = ω^ (ω↑↑ i)

ω↑↑-↑ : increasing ω↑↑
ω↑↑-↑  0      = subst (λ z → one < z) (sym ω^one≡ω) (<-cocone-simple ι {k = 1})
ω↑↑-↑ (suc i) = ω^-mono-< (ω↑↑-↑ i)

ε₀ : Brw
ε₀ = limit ω↑↑ {ω↑↑-↑}

ε₀≡ω^ε₀ : ε₀ ≡ ω^ ε₀
ε₀≡ω^ε₀ = ≤-antisym (weakly-bisimilar→lim≤lim ω↑↑ (λ n → limit ι ^ ω↑↑ n)
                                              (λ k → ∣ k , a<omega^a ∣))
                    (weakly-bisimilar→lim≤lim (λ n → limit ι ^ ω↑↑ n) ω↑↑
                                              (λ k → ∣ suc k , ≤-refl ∣))
