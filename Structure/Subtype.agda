
module Structure.Subtype {a ℓ} {A : Set a} where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)

_\[_] : (S : A → Set ℓ) → (R : A → Set ℓ) → A → Set ℓ
S \[ R ] = λ x → (S x) × (¬ (R x))

data ⊤ : Set ℓ where
  true : ⊤

nonProperSubtype : A → Set ℓ
nonProperSubtype _ = ⊤
