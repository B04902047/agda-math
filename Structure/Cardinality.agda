
module Structure.Cardinality {A : Set} (_≈_ : A → A → Set) where

open import Structure.Properties
open import Structure.Setoid
open import Structure.Equality
open import Structure.Morphism
open import Structure.Subtype
open import Structure.Logic
open import Data.Nat
open import Data.List hiding ([_])


record IsCountable  (S : A → Set) : Set₁ where
  field
    isSet       : IsSet _≈_ S
    f           : A → ℕ
    injectivity : Injective _≈_ _≡_ f S (λ x → ℕ) isSet (≡-isSet (λ x → ℕ))

record IsInfinite (S : A → Set) : Set₁ where
  field
    isSet       : IsSet _≈_ S
    f           : ℕ → A
    injectivity : Injective _≡_ _≈_ f (λ x → ℕ) S (≡-isSet (λ x → ℕ)) isSet

record IsFinite (S : A → Set) : Set₁ where
  field
    isCountable : IsCountable S
    N           : ℕ
    finite      : {x : A} → S x → (IsCountable.f isCountable x) ≤ N

  open IsCountable isCountable
  postulate
    size : ℕ
