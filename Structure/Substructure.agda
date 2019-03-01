
module Structure.Substructure {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) (S : A → Set ℓ) where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)

S\[_] : A → A → Set ℓ
S\[ c ] x = (S x) × (¬ (x ≈ c))
