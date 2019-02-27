
module Semigroup {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) (S : A → Set ℓ) where

open import Properties _≈_ S
open import Setoid _≈_ S public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


record IsMagma (∙ : A → A → A) : Set (a ⊔ ℓ) where
  field
    isSetoid  : IsSetoid
    _∙-close_ : Closed₂ ∙
    ∙-cong    : Congruent₂ ∙

  open IsSetoid isSetoid public

  ∙-congˡ : LeftCongruent ∙
  ∙-congˡ x∈S y∈S z∈S x≈y = ∙-cong x∈S y∈S z∈S z∈S x≈y (refl z∈S)

  ∙-congʳ : RightCongruent ∙
  ∙-congʳ x∈S y∈S z∈S x≈y = ∙-cong z∈S z∈S x∈S y∈S (refl z∈S) x≈y

record IsSemigroup (∙ : A → A → A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    ∙-assoc   : Associative ∙

  open IsMagma isMagma public
--
record IsBand (∙ : A → A → A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    idem        : Idempotent ∙

  open IsSemigroup isSemigroup public

record IsSemilattice (∧ : A → A → A) : Set (a ⊔ ℓ) where
  field
    isBand : IsBand ∧
    comm   : Commutative ∧

  open IsBand isBand public renaming (∙-cong to ∧-cong)
