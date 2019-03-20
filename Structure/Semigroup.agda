
module Structure.Semigroup
        {A : Set}
        (_≈_ : A → A → Set) where

open import Structure.Subtype
open import Structure.Properties _≈_
open import Structure.Setoid _≈_ public
open import Structure.Logic


record IsMagma (M : A → Set) (_∙_ : A → A → A)
                        : Set₁ where
  field
    isSet     : IsSet M
    _∙-close_ : Closed₂ M _∙_

  open IsSet isSet public

  ∙-congˡ : LeftCongruent M _∙_
  ∙-congˡ {x} {y} {z} x∈M y∈M z∈M = ap (_∙ z) x∈M y∈M

  ∙-congʳ : RightCongruent M _∙_
  ∙-congʳ  {x} {y} {z} x∈M y∈M z∈M = ap (z ∙_ ) x∈M y∈M

  ∙-sum : (S T : A → Set) → A → Set
  ∙-sum S T z
    = Σ[ x ∈ A ] (Σ[ y ∈ A ] ((S x) × ((T y) × ((x ∙ y) ≈ z))))

record _IsSubmagmaOf_
          (N : A → Set)
          (M : A → Set)
          (∙ : A → A → A) : Set₁ where
  field
    N⊆M         : N ⊆ M
    M-isMagma   : IsMagma M ∙
    _∙-close-N_ : Closed₂ N ∙
  open IsMagma M-isMagma

  N-isSubsetOf-M : N IsSubsetOf M
  N-isSubsetOf-M = record
    { T⊆S     = N⊆M
    ; S-isSet = isSet
    }

  isSet-N : IsSet N
  isSet-N = _IsSubsetOf_.T-isSet N-isSubsetOf-M

  N-isMagma : IsMagma N ∙
  N-isMagma = record
    { isSet  = isSet-N
    ; _∙-close_ = _∙-close-N_
    }

record IsSemigroup (S : A → Set) (∙ : A → A → A)
                                      : Set₁ where
  field
    isMagma : IsMagma S ∙
    ∙-assoc   : Associative S ∙

  open IsMagma isMagma public

record _IsSubsemigroupOf_
          (T : A → Set) (S : A → Set)
          (∙ : A → A → A) : Set₁ where
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

record IsBand (B : A → Set) (∙ : A → A → A)
                            : Set₁ where
  field
    isSemigroup : IsSemigroup B ∙
    idem        : Idempotent B ∙

  open IsSemigroup isSemigroup public

record IsSemilattice (S : A → Set) (∧ : A → A → A)
                            : Set₁  where
  field
    isBand : IsBand S ∧
    comm   : Commutative S ∧

  open IsBand isBand public
    renaming
      ( ∙-congˡ to ∧-congˡ
      ; ∙-congʳ to ∧-congʳ
      )
