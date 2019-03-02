
module Structure.Semigroup
        {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) where

open import Structure.Properties _≈_
open import Structure.Equivalence public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


record IsMagma (S : A → Set ℓ) (∙ : A → A → A)
                                        : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_ S
    _∙-close_     : Closed₂ S ∙
    ∙-cong        : Congruent₂ S ∙

  open IsEquivalence isEquivalence public

  ∙-congˡ : LeftCongruent S ∙
  ∙-congˡ x∈S y∈S z∈S x≈y = ∙-cong x∈S y∈S z∈S z∈S x≈y (refl z∈S)

  ∙-congʳ : RightCongruent S ∙
  ∙-congʳ x∈S y∈S z∈S x≈y = ∙-cong z∈S z∈S x∈S y∈S (refl z∈S) x≈y

record IsSemigroup (S : A → Set ℓ) (∙ : A → A → A)
                                      : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma S ∙
    ∙-assoc   : Associative S ∙

  open IsMagma isMagma public

record IsBand (S : A → Set ℓ) (∙ : A → A → A)
                                      : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup S ∙
    idem        : Idempotent S ∙

  open IsSemigroup isSemigroup public

record IsSemilattice (S : A → Set ℓ) (∧ : A → A → A)
                                      : Set (a ⊔ ℓ) where
  field
    isBand : IsBand S ∧
    comm   : Commutative S ∧

  open IsBand isBand public renaming (∙-cong to ∧-cong)
