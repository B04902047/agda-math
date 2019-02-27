
module Setoid {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) (S : A → Set ℓ) where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)
open import Properties _≈_ S

record IsSetoid : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence

  open IsEquivalence isEquivalence public
  open import EquivalenceReasoning _≈_ S refl sym trans public
    renaming
    ( _∼⟨_,_⟩_ to _≈⟨_,_⟩_
    ; _∼˘⟨_,_⟩_ to _≈˘⟨_,_⟩_
    )
