
open import Basic.Properties using (Reflexive; Symmetric; Transitive)

module Reasoning.Equivalence
  {A : Set}
  (_≈_ : A → A → Set)
  (S : A → Set)
  (refl : Reflexive _≈_ S)
  (sym : Symmetric _≈_ S)
  (trans : Transitive _≈_ S)
  where

open import Reasoning.Preorder _≈_ S refl trans public
  renaming
    ( _IsWeakerThan_ to _IsEquivalentTo_
    ; _≤⟨_,_⟩_ to _≈⟨_,_⟩_
    )

infixr 2 _≈˘⟨_,_⟩_

_≈˘⟨_,_⟩_ : ∀ x {y z} → S x → y ≈ x → y IsEquivalentTo z → x IsEquivalentTo z
_ ≈˘⟨ x∈S , y≈x ⟩ equivTo = _ ≈⟨ x∈S , (sym y∈S x∈S y≈x) ⟩ equivTo
  where y∈S = _IsEquivalentTo_.1∈S equivTo
