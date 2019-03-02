
module Structure.Monoid {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) where

open import Structure.Properties _≈_
open import Structure.Semigroup _≈_ public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


record IsMonoid (M : A → Set ℓ) (_∙_ : A → A → A) (ε : A)
                                        : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup M _∙_
    ε-close     : Closed₀ M ε
    ε-identity  : Identity M _∙_ ε

  open IsSemigroup isSemigroup public

  ε-identityˡ : LeftIdentity M _∙_ ε
  ε-identityˡ = proj₁ ε-identity

  _ε-identityʳ : RightIdentity M _∙_ ε
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
          (M : A → Set ℓ) (_∙_ : A → A → A) (ε : A)
                                      : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup M _∙_
    ε-close     : Closed₀ M ε
    ε-identityˡ : LeftIdentity M _∙_ ε
    ∙-comm      : Commutative M _∙_

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
          (M : A → Set ℓ) (∙ : A → A → A) (ε : A)
                                      : Set (a ⊔ ℓ) where
  field
    isCommutativeMonoid : IsCommutativeMonoid M ∙ ε
    idem                : Idempotent M ∙

  open IsCommutativeMonoid isCommutativeMonoid public
