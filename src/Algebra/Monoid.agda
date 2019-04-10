
module Algebra.Monoid
        {A : Set}
        (_≈_ : A → A → Set) where

open import Algebra.Semigroup _≈_ public

open import Basic.Logic
open import Basic.Properties _≈_
open import Basic.Subtype

record IsMonoid (M : A → Set) (_∙_ : A → A → A) (ε : A)
                                  : Set₁ where
  field
    isSemigroup : IsSemigroup M _∙_
    ε∈M         : M ε
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
                        ≈⟨ e∈M ∙-close ε∈M , λx∈M→e∙x≈x ε∈M ⟩
                          ε
                        ∎⟨ ε∈M ⟩
  ε-uniqueʳ : {e : A} → M e → ({x : A} → M x → ((x ∙ e) ≈ x)) → (e ≈ ε)
  ε-uniqueʳ {e} e∈M λx∈M→x∙e≈x = begin
                          e
                        ≈˘⟨ e∈M , ε-identityˡ e∈M ⟩
                          ε ∙ e
                        ≈⟨ ε∈M ∙-close e∈M , λx∈M→x∙e≈x ε∈M ⟩
                          ε
                        ∎⟨ ε∈M ⟩

record IsCommutativeMonoid
          (M : A → Set) (_∙_ : A → A → A) (ε : A) : Set₁ where
  field
    isSemigroup : IsSemigroup M _∙_
    ε∈M     : Closed₀ M ε
    ε-identityˡ : LeftIdentity M _∙_ ε
    _∙-comm_    : Commutative M _∙_

  open IsSemigroup isSemigroup public

  ε-identityʳ : RightIdentity M _∙_ ε
  ε-identityʳ {x} x∈M = begin
                        x ∙ ε
                      ≈⟨ x∈M ∙-close ε∈M , x∈M ∙-comm ε∈M ⟩
                        ε ∙ x
                      ≈⟨ ε∈M ∙-close x∈M ,  ε-identityˡ x∈M ⟩
                        x
                      ∎⟨ x∈M ⟩

  ε-identity : Identity M _∙_ ε
  ε-identity = (ε-identityˡ , ε-identityʳ)

  isMonoid : IsMonoid M _∙_ ε
  isMonoid = record {
      isSemigroup = isSemigroup
    ; ε∈M     = ε∈M
    ; ε-identity    = ε-identity
    }

record IsIdempotentCommutativeMonoid
              (M : A → Set) (∙ : A → A → A) (ε : A)
                                : Set₁ where
  field
    isCommutativeMonoid : IsCommutativeMonoid M ∙ ε
    idem                : Idempotent M ∙

  open IsCommutativeMonoid isCommutativeMonoid public


record _IsSubmonoidOf_
        (N M : A → Set)
        (_∙_ : A → A → A) (ε : A)
                            : Set₁ where
  field
    N⊆M        : N ⊆ M
    M-isMonoid : IsMonoid M _∙_ ε
    N-isMonoid : IsMonoid N _∙_ ε

record _IsSubmonoidOf'_
        (N M : A → Set)
        (_∙_ : A → A → A) (ε : A)
                            : Set₁ where
  field
    N⊆M         : N ⊆ M
    M-isMonoid  : IsMonoid M _∙_ ε
    ε∈M-N   : N ε
    _∙-close-N_ : Closed₂ N _∙_

  open IsMonoid M-isMonoid
    renaming (isSemigroup to M-isSemigroup)

  N-isSubsemigroupOf-M : (N IsSubsemigroupOf M) _∙_
  N-isSubsemigroupOf-M = record
    { T⊆S           = N⊆M
    ; S-isSemigroup = M-isSemigroup
    ; _∙-close-T_    = _∙-close-N_
    }

  N-isSemigroup : IsSemigroup N _∙_
  N-isSemigroup = _IsSubsemigroupOf_.T-isSemigroup N-isSubsemigroupOf-M

  ε-identityˡ-N : LeftIdentity N _∙_ ε
  ε-identityˡ-N x∈N = ε-identityˡ (N⊆M x∈N)

  _ε-identityʳ-N : RightIdentity N _∙_ ε
  x∈N ε-identityʳ-N  = (N⊆M x∈N) ε-identityʳ

  ε-identity-N : Identity N _∙_ ε
  ε-identity-N = (ε-identityˡ-N , _ε-identityʳ-N)

  N-isMonoid : IsMonoid N _∙_ ε
  N-isMonoid = record
    { isSemigroup = N-isSemigroup
    ; ε∈M     = ε∈M-N
    ; ε-identity  = ε-identity-N
    }
