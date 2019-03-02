
module Structure.Product
        {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) where

open import Structure.Properties
--import Structure.Group _≈ᵍ_ as ⟨A,≈ᵍ⟩
import Structure.Field _≈_
open import Data.Nat
open import Data.Vec

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

--Π

data ⊤ : Set ℓ where
  tt : ⊤

Tuple : (S : A → Set ℓ) → (n : ℕ) → Vec A n → Set ℓ
Tuple S n [] = ⊤
Tuple S (suc n) (x ∷ xs) = (S x) × (Tuple S n xs)


-- record Tuple (F : A → Set ℓ)
--           (_+_ _*_ : A → A → A)
--           (0# 1# : A) (- _⁻¹ : A → A) (n : ℕ) : Set where
--   field
--     isField : IsField F _+_ _*_ 0# 1# - _⁻¹
--
--   _+ⁿ_ :
