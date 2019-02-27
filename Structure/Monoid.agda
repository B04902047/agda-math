
module Monoid {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) (M : A → Set ℓ) where

open import Properties _≈_ M
open import Semigroup _≈_ M public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


record IsMonoid (_∙_ : A → A → A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup _∙_
    ε-close     : Closed₀ ε
    ε-identity  : Identity _∙_ ε

  open IsSemigroup isSemigroup public

  ε-identityˡ : LeftIdentity _∙_ ε
  ε-identityˡ = proj₁ ε-identity

  _ε-identityʳ : RightIdentity _∙_ ε
  _ε-identityʳ = proj₂ ε-identity

  ε-uniqueˡ : {e : A} → M e → ({x : A} → M x → ((e ∙ x) ≈ x)) → (e ≈ ε)
  ε-uniqueˡ {e} e∈M λx∈M→e∙x≈x = begin
                          e
                        ≈˘⟨ e∈M , e∈M ε-identityʳ ⟩
                          e ∙ ε
                        ≈⟨ e∈M ∙-close ε-close , λx∈M→e∙x≈x ε-close ⟩
                          ε
                        ∎⟨ ε-close ⟩
  ε-uniqueʳ : {e : A} → M e → ({x : A} → M x → ((x ∙ e) ≈ x)) → (e ≈ ε)
  ε-uniqueʳ {e} e∈M λx∈M→x∙e≈x = begin
                          e
                        ≈˘⟨ e∈M , ε-identityˡ e∈M ⟩
                          ε ∙ e
                        ≈⟨ ε-close ∙-close e∈M , λx∈M→x∙e≈x ε-close ⟩
                          ε
                        ∎⟨ ε-close ⟩

record IsCommutativeMonoid
            (_∙_ : A → A → A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup _∙_
    ε-close     : Closed₀ ε
    ε-identityˡ : LeftIdentity _∙_ ε
    ∙-comm      : Commutative _∙_

  open IsSemigroup isSemigroup public

  -- postulate
  --   identityʳ : RightIdentity _∙_ ε
  --
  -- identity : Identity _∙_ ε
  -- identity = (identityˡ , identityʳ)
  --
  -- isMonoid : IsMonoid _∙_ ε
  -- isMonoid = record {
  --     isSemigroup = isSemigroup
  --   ; ε-close     = ε-close
  --   ; identity    = identity
  --   }

record IsIdempotentCommutativeMonoid
                (∙ : A → A → A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeMonoid : IsCommutativeMonoid ∙ ε
    idem                : Idempotent ∙

  open IsCommutativeMonoid isCommutativeMonoid public
