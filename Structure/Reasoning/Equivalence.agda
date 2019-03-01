
open import Structure.Properties using (Reflexive; Symmetric; Transitive)

module Structure.Reasoning.Equivalence
  {a ℓ} {A : Set a}
  (_≈_ : A → A → Set ℓ) (S : A → Set ℓ)
  (refl : Reflexive _≈_ S)
  (sym : Symmetric _≈_ S)
  (trans : Transitive _≈_ S)
  where

open import Structure.Reasoning.Preorder _≈_ S refl trans public
  renaming
    ( _IsWeakerThan_ to _IsEquivalentTo_
    ; _≤⟨_,_⟩_ to _≈⟨_,_⟩_
    )

infixr 2 _≈˘⟨_,_⟩_

_≈˘⟨_,_⟩_ : ∀ x {y z} → S x → y ≈ x → y IsEquivalentTo z → x IsEquivalentTo z
_ ≈˘⟨ sx , y≈x ⟩ equivTo = _ ≈⟨ sx , (sym sy sx y≈x) ⟩ equivTo
  where sy = _IsEquivalentTo_.s1 equivTo
