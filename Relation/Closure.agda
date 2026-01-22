----------------------------------------------------------------------------------------------------
-- Transitive and reflexive-transitive closures
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness --safe #-}
module Relation.Closure where

open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)

open import PropTrunc

module _ {ℓ ℓ' : Level}{A : Type ℓ}(_≺_ : A -> A -> Type ℓ') where

  data TransCl : A → A → Type (ℓ-max ℓ ℓ') where
    emb : ∀ {x y : A} → x ≺ y → TransCl x y
    step : ∀ {x y z : A} → x ≺ y → TransCl y z → TransCl x z

  data ReflTransCl : A → A → Type (ℓ-max ℓ ℓ') where
    done : ∀ {x : A} → ReflTransCl x x
    step : ∀ {x y z : A} → x ≺ y → ReflTransCl y z → ReflTransCl x z

  Trans→ReflTrans : ∀ {x y} → TransCl x y → ReflTransCl x y
  Trans→ReflTrans (emb x<y) = step x<y done
  Trans→ReflTrans (step x<y p) = step x<y (Trans→ReflTrans p)

  TransCl-trans : ∀ {x y z} → TransCl x y → TransCl y z → TransCl x z
  TransCl-trans (emb x) q = step x q
  TransCl-trans (step x p) q = step x (TransCl-trans p q)

  ReflTransCl-trans : ∀ {x y z} → ReflTransCl x y → ReflTransCl y z → ReflTransCl x z
  ReflTransCl-trans done q = q
  ReflTransCl-trans (step x p) q = step x (ReflTransCl-trans p q)

  ReflTransTransCl-trans : ∀ {x y z} → ReflTransCl x y → TransCl y z → TransCl x z
  ReflTransTransCl-trans done qs = qs
  ReflTransTransCl-trans (step p ps) qs = step p (ReflTransTransCl-trans ps qs)

  embRT : ∀ {x y : A} → x ≺ y → ReflTransCl x y
  embRT p = step p done

  stepT : ∀ {x y z : A} → x ≺ y → ReflTransCl y z → TransCl x z
  stepT x<y done = emb x<y
  stepT x<y (step y<y' y'<*z) = step x<y (stepT y<y' y'<*z)

  TransClWellfounded : isWellFounded _≺_ → isWellFounded TransCl
  TransClWellfounded wf x = lemma x (wf x)
    where
      lemma : (y : A) → Acc _≺_ y → Acc TransCl y
      lemma y (acc s) = acc g where
        g : (z : A) → TransCl z y → Acc TransCl z
        g z (emb p) = lemma z (s z p)
        g z (step p ps) = access (g _ ps) z (emb p)

∥∥-wellfounded : ∀ {ℓ ℓ'} → {A : Type ℓ}{_≺_ : A -> A -> Type ℓ'} →
                isWellFounded _≺_ → isWellFounded (λ x y → ∥ x ≺ y ∥)
∥∥-wellfounded {_≺_ = _≺_} wf x = lemma x (wf x)
  where
    lemma : ∀ x → Acc _≺_ x → Acc (λ x y → ∥ x ≺ y ∥) x
    lemma x (acc s) = acc λ y → ∥-∥rec (isPropAcc y) λ y<x → lemma y (s y y<x)

∥TransCl∥-wellfounded : ∀ {ℓ ℓ'} → {A : Type ℓ}{_≺_ : A -> A -> Type ℓ'} →
                       isWellFounded _≺_ → isWellFounded (λ x y → ∥ TransCl _≺_ x y ∥)
∥TransCl∥-wellfounded wf = ∥∥-wellfounded (TransClWellfounded _ wf)

TransCl-map : ∀ {ℓ ℓ'} → {A : Type ℓ}{B : Type ℓ'} →
              {_<A_ : A -> A -> Type ℓ} → {_<B_ : B -> B -> Type ℓ'} →
              (f : A → B) → ({x y : A} → x <A y → f x <B f y) →
              {x y : A} → TransCl _<A_ x y → TransCl _<B_ (f x) (f y)
TransCl-map f g (emb p) = emb (g p)
TransCl-map f g (step p ps) = step (g p) (TransCl-map f g ps)

ReflTransCl-map : ∀ {ℓ ℓ'} → {A : Type ℓ}{B : Type ℓ'} →
              {_<A_ : A -> A -> Type ℓ} → {_<B_ : B -> B -> Type ℓ'} →
              (f : A → B) → ({x y : A} → x <A y → f x <B f y) →
              {x y : A} → ReflTransCl _<A_ x y → ReflTransCl _<B_ (f x) (f y)
ReflTransCl-map f g done = done
ReflTransCl-map f g (step p ps) = step (g p) (ReflTransCl-map f g ps)
