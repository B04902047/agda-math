
module Number.Cardinality {A : Set} (_≈_ : A → A → Set) where

open import Basic.Properties
open import Basic.Setoid
open import Basic.Equality
open import Basic.Morphism
open import Basic.Subtype
open import Basic.Logic
open import Data.Nat
open import Data.List hiding ([_])


record IsCountable (S : A → Set) : Set₁ where
  field
    f             : A → ℕ
    f-isFunction  : IsFunction f _≈_ S _≡_ (nonProper {ℕ})
    f-injectivity : IsFunction.Injective f-isFunction

record IsInfinite (S : A → Set) : Set₁ where
  field
    f             : ℕ → A
    f-isFunction  : IsFunction f _≡_ (nonProper {ℕ}) _≈_ S
    f-injectivity : IsFunction.Injective f-isFunction

record IsFinite (S : A → Set) : Set₁ where
  field
    isCountable : IsCountable S
    N           : ℕ
    finiteness  : {x : A} → S x
                → (IsCountable.f isCountable x) ≤ N

  open IsCountable isCountable
  postulate
    size : ℕ
