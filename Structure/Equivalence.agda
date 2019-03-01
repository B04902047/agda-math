
module Structure.Equivalence {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) (S : A → Set ℓ) where

open import Structure.Properties _≈_ S

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

record IsEquivalence : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive
    sym   : Symmetric
    trans : Transitive
  open import Structure.Reasoning.Equivalence _≈_ S refl sym trans public
