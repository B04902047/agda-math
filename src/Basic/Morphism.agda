
module Basic.Morphism
        {A : Set} {B : Set}
        (_≈₁_ : A → A → Set)
        (_≈₂_ : B → B → Set) where

open import Basic.Setoid
open import Basic.Logic

Injective : (f : A → B) → (S₁ : A → Set) → (S₂ : B → Set)
            → (IsSet _≈₁_ S₁) → (IsSet _≈₂_ S₂)
            → Set
Injective f S₁ S₂ _ _ = {x y : A} → S₁ x → S₁ y
                    → ¬ (x ≈₁ y) → ¬ ((f x) ≈₂ (f y))

Surjective : (f : A → B) → (S₁ : A → Set) → (S₂ : B → Set)
            → (IsSet _≈₂_ S₂)
            → Set
Surjective f S₁ S₂ _ = {y : B} → S₂ y
                    → Σ[ x ∈ A ] ((S₁ x) × ((f x) ≈₂ y))

Bijective : (f : A → B) → (S₁ : A → Set) → (S₂ : B → Set)
            → (IsSet _≈₁_ S₁) → (IsSet _≈₂_ S₂)
            → Set
Bijective f S₁ S₂ isEquivalence₁ isEquivalence₂
  = (Injective f S₁ S₂ isEquivalence₁ isEquivalence₂)
    × (Surjective f S₁ S₂ isEquivalence₂)
