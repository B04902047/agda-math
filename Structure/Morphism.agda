
module Structure.Morphism
        {a b ℓ₁ ℓ₂}
        {A : Set a} {B : Set b}
        (_≈₁_ : A → A → Set ℓ₁)
        (_≈₂_ : B → B → Set ℓ₂) where

open import Structure.Equivalence
open import Data.Product
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

Injective : (f : A → B) → (S₁ : A → Set ℓ₁) → (S₂ : B → Set ℓ₂)
            → (IsEquivalence _≈₁_ S₁) → (IsEquivalence _≈₂_ S₂)
            → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Injective f S₁ S₂ _ _ = {x y : A} → S₁ x → S₁ y
                    → ¬ (x ≈₁ y) → ¬ ((f x) ≈₂ (f y))

Surjective : (f : A → B) → (S₁ : A → Set ℓ₁) → (S₂ : B → Set ℓ₂)
            → (IsEquivalence _≈₂_ S₂)
            → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Surjective f S₁ S₂ _ = {y : B} → S₂ y
                    → Σ[ x ∈ A ] ((S₁ x) × ((f x) ≈₂ y))

Bijective : (f : A → B) → (S₁ : A → Set ℓ₁) → (S₂ : B → Set ℓ₂)
            → (IsEquivalence _≈₁_ S₁) → (IsEquivalence _≈₂_ S₂)
            → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Bijective f S₁ S₂ isEquivalence₁ isEquivalence₂
  = (Injective f S₁ S₂ isEquivalence₁ isEquivalence₂)
    × (Surjective f S₁ S₂ isEquivalence₂)
