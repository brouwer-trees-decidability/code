{-# OPTIONS --cubical --erasure --guardedness  #-}
module Bool where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as N
import Cubical.Data.Nat.Order as N

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Bool as B renaming (_≤_ to _B≤_) public

Bool→Nat :  Bool → ℕ
Bool→Nat false = 0
Bool→Nat true = 1

Bool→Nat-mono : {u v : Bool} → u B≤ v → Bool→Nat u N.≤ Bool→Nat v
Bool→Nat-mono {false} {v} p = N.zero-≤
Bool→Nat-mono {true} {true} p = N.≤-refl

Bool≤true : {s : Bool} → s B≤ true
Bool≤true {false} = tt
Bool≤true {true} = tt

Bool-true≤→≡ : {s : Bool} → true B≤ s → true ≡ s
Bool-true≤→≡ {false} p = ⊥.rec p
Bool-true≤→≡ {true} p = refl

Bool≡→≤ : {v u : Bool} → v ≡ u → v B≤ u
Bool≡→≤ {false} {u} p = tt
Bool≡→≤ {true} {false} p = not≢const false p
Bool≡→≤ {true} {true} p = tt

Boolx≤y∧x≡t→y=t : {x y : Bool} → x B≤ y → x ≡ true → y ≡ true
Boolx≤y∧x≡t→y=t {x} {y} p q = sym (Bool-true≤→≡ (subst (λ z → z B≤ y) q p))

Boolx≡t∧y=t→x≤y : {x y : Bool} → (x ≡ true → y ≡ true) → x B≤ y
Boolx≡t∧y=t→x≤y {false} p = _
Boolx≡t∧y=t→x≤y {true} p = subst (true B≤_) (sym (p refl)) _

Bool≤-trans : {u v s : Bool} → u B≤ v  → v B≤ s → u B≤ s
Bool≤-trans {false} {v} {s} p q = tt
Bool≤-trans {true} {true} {s} p q = q

Bool-≤-refl : {u : Bool} → u B≤ u
Bool-≤-refl = Bool≡→≤ refl

Bool-≤-or : {x y z : Bool} → x B≤ y → x B≤ (y or z)
Bool-≤-or {false} p = tt
Bool-≤-or {true} {true} p = tt

Bool-≤-or-2 : {x y z : Bool} → x B≤ y → x B≤ (z or y)
Bool-≤-or-2 {false} p = tt
Bool-≤-or-2 {true} {true} {false} p = tt
Bool-≤-or-2 {true} {true} {true} p = tt

Bool-or-introL : {x y : Bool} → x ≡ true → x or y ≡ true
Bool-or-introL {false} p = ⊥.rec (false≢true p)
Bool-or-introL {true} p = p

Bool-or-introR : {x y : Bool} → y ≡ true → x or y ≡ true
Bool-or-introR {false} p = p
Bool-or-introR {true} p = refl

Dec→Bool≡true : {ℓ : Level} (A : Type ℓ) → A → (d : Dec A) → Dec→Bool d ≡ true
Dec→Bool≡true A a (yes p) = refl
Dec→Bool≡true A a (no ¬p) = ⊥.rec (¬p a)
