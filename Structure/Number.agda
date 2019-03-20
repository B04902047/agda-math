
module Structure.Number {A : Set} (_≈_ : A → A → Set) where

open import Structure.Properties
open import Structure.Setoid
open import Structure.Equality
open import Structure.Morphism
open import Structure.Subtype
open import Data.Nat
open import Structure.Logic

-- data ℕ : Set where
--   0# : ℕ
--   1+ : ℕ → ℕ
--
-- data _≤_ : ℕ → ℕ → Set where
--   0≤n : (n : ℕ) → 0# ≤ n
--   s≤s : (n : ℕ) → n ≤ (1+ n)

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
