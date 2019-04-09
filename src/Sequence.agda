
module Number.Sequence where

open import Basic.Morphism
open import Basic.Setoid
open import Basic.Logic
open import Basic.Subtype

open import Number.Natural


IsSequence : {A : Set} (f : ℕ → A)
            → (_≈_ : A → A → Set)
            → (S : A → Set)
            → Set₁
IsSequence f _≈_ S = IsFunction f _≡ᴺ_ nonProper _≈_ S
