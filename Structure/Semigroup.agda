
module Structure.Semigroup
        {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) where

open import Structure.Subtype
open import Structure.Properties _≈_
open import Structure.Setoid _≈_ public

open import Structure.Logic
open import Level using (_⊔_; suc)


record IsMagma (M : A → Set ℓ) (_∙_ : A → A → A)
                                        : Set (a ⊔ suc ℓ) where
  field
    isSetoid  : IsSetoid M
    _∙-close_ : Closed₂ M _∙_

  open IsSetoid isSetoid public

  ∙-congˡ : LeftCongruent M _∙_
  ∙-congˡ {x} {y} {z} x∈M y∈M z∈M = ap (_∙ z) x∈M y∈M

  ∙-congʳ : RightCongruent M _∙_
  ∙-congʳ  {x} {y} {z} x∈M y∈M z∈M = ap (z ∙_ ) x∈M y∈M

record _IsSubmagmaOf_ (N : A → Set ℓ) (M : A → Set ℓ)
                    (∙ : A → A → A) : Set (a ⊔ suc ℓ) where
  field
    N⊆M         : N ⊆ M
    M-isMagma   : IsMagma M ∙
    _∙-close-N_ : Closed₂ N ∙
  open IsMagma M-isMagma

  N-isSubsetoidOf-M : N IsSubsetoidOf M
  N-isSubsetoidOf-M = record
    { T⊆S        = N⊆M
    ; S-isSetoid = isSetoid
    }

  isSetoid-N : IsSetoid N
  isSetoid-N = _IsSubsetoidOf_.T-isSetoid N-isSubsetoidOf-M

  N-isMagma : IsMagma N ∙
  N-isMagma = record
    { isSetoid  = isSetoid-N
    ; _∙-close_ = _∙-close-N_
    }

record IsSemigroup (S : A → Set ℓ) (∙ : A → A → A)
                                      : Set (a ⊔ suc ℓ) where
  field
    isMagma : IsMagma S ∙
    ∙-assoc   : Associative S ∙

  open IsMagma isMagma public

record _IsSubsemigroupOf_ (T : A → Set ℓ) (S : A → Set ℓ)
                        (∙ : A → A → A) : Set (a ⊔ suc ℓ) where
  field
    T⊆S : T ⊆ S
    S-isSemigroup : IsSemigroup S ∙
    _∙-close-T_ : Closed₂ T ∙

  open IsSemigroup S-isSemigroup
    renaming (isMagma to S-isMagma)

  T-isSubmagmaOf-S : (T IsSubmagmaOf S) ∙
  T-isSubmagmaOf-S = record
    { N⊆M         = T⊆S
    ; M-isMagma   = S-isMagma
    ; _∙-close-N_ = _∙-close-T_
    }

  T-isMagma : IsMagma T ∙
  T-isMagma = _IsSubmagmaOf_.N-isMagma T-isSubmagmaOf-S

  ∙-assoc-T : Associative T ∙
  ∙-assoc-T x∈T y∈T z∈T = ∙-assoc (T⊆S x∈T) (T⊆S y∈T) (T⊆S z∈T)

  T-isSemigroup : IsSemigroup T ∙
  T-isSemigroup = record
    { isMagma = T-isMagma
    ; ∙-assoc = ∙-assoc-T
    }

record IsBand (S : A → Set ℓ) (∙ : A → A → A)
                                      : Set (a ⊔ suc ℓ) where
  field
    isSemigroup : IsSemigroup S ∙
    idem        : Idempotent S ∙

  open IsSemigroup isSemigroup public

record IsSemilattice (S : A → Set ℓ) (∧ : A → A → A)
                                      : Set (a ⊔ suc ℓ) where
  field
    isBand : IsBand S ∧
    comm   : Commutative S ∧

  open IsBand isBand public
    renaming
      ( ∙-congˡ to ∧-congˡ
      ; ∙-congʳ to ∧-congʳ
      )
