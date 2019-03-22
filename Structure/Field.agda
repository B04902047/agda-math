
module Structure.Field {A : Set} (_≈_ : A → A → Set) where

open import Structure.Properties _≈_
open import Structure.DivisionRing _≈_
open import Structure.Subtype
open import Structure.Logic


record IsField
      (F : A → Set) (_+_ _*_ : A → A → A)
      (0# 1# : A) (- _⁻¹ : A → A) : Set₁ where
  field
    isDivisionRing : IsDivisionRing F _+_ _*_ 0# 1# - _⁻¹
    _*-comm_       : Commutative F _*_
    1≉0           : ¬ (1# ≈ 0#)

  open IsDivisionRing isDivisionRing public

  noNonzeroZeroDivisors : {x y : A} → F x → F y
                        → ¬ (x ≈ 0#) → ¬ (y ≈ 0#)
                        → ¬ ((x * y) ≈ 0#)
  noNonzeroZeroDivisors {x} {y} x∈F y∈F x≉0 y≉0 x*y≈0
    = 1≉0 1≈0 --≉
    where
      1≈0 = begin
            1#
          ≈˘⟨ 1∈F , 1∈F 1-identityʳ ⟩
            1# * 1#
          ≈˘⟨ 1∈F *-close 1∈F , *-congˡ x⁻¹*x∈F 1∈F 1∈F ((x∈F , x≉0) ⁻¹-inverse\[0]ˡ) ⟩
            ((x ⁻¹) * x) * 1#
          ≈˘⟨ x⁻¹*x∈F *-close 1∈F , *-congʳ (y∈F *-close y⁻¹∈F) 1∈F x⁻¹*x∈F ((y∈F , y≉0) ⁻¹-inverse\[0]ʳ) ⟩
            ((x ⁻¹) * x) * (y * (y ⁻¹))
          ≈˘⟨ x⁻¹*x∈F *-close (y∈F *-close y⁻¹∈F) , *-assoc x⁻¹*x∈F y∈F y⁻¹∈F ⟩
            (((x ⁻¹) * x) * y) * (y ⁻¹)
          ≈⟨ (x⁻¹*x∈F *-close y∈F) *-close y⁻¹∈F , *-congˡ (x⁻¹*x∈F *-close y∈F) (x⁻¹∈F *-close (x∈F *-close y∈F)) y⁻¹∈F (*-assoc x⁻¹∈F x∈F y∈F) ⟩
            ((x ⁻¹) * (x * y)) * (y ⁻¹)
          ≈⟨ (x⁻¹∈F *-close (x∈F *-close y∈F)) *-close y⁻¹∈F , *-congˡ (x⁻¹∈F *-close (x∈F *-close y∈F)) (x⁻¹∈F *-close 0∈F) y⁻¹∈F (*-congʳ (x∈F *-close y∈F) 0∈F x⁻¹∈F x*y≈0) ⟩
            ((x ⁻¹) * 0#) * (y ⁻¹)
          ≈⟨ (x⁻¹∈F *-close 0∈F) *-close y⁻¹∈F , *-congˡ (x⁻¹∈F *-close 0∈F) 0∈F y⁻¹∈F (x⁻¹∈F 0-zeroʳ) ⟩
            0# * (y ⁻¹)
          ≈⟨ 0∈F *-close y⁻¹∈F , 0-zeroˡ y⁻¹∈F ⟩
            0#
          ∎⟨ 0-close ⟩
          where
            1∈F = 1-close
            0∈F = 0-close
            x⁻¹∈F = proj₁ ((x∈F , x≉0) ⁻¹-close\[0])
            x⁻¹≉0 = proj₂ ((x∈F , x≉0) ⁻¹-close\[0])
            y⁻¹∈F = proj₁ ((y∈F , y≉0) ⁻¹-close\[0])
            y⁻¹≉0 = proj₂ ((y∈F , y≉0) ⁻¹-close\[0])
            x⁻¹*x∈F = x⁻¹∈F *-close x∈F

  isIntegralDomain : IsIntegralDomain F _+_ _*_ 0# 1# -
  isIntegralDomain = record
    { isRing                = isRing
    ; noNonzeroZeroDivisors = noNonzeroZeroDivisors
    }

  postulate
    ix : {x : A} → F x → ¬ (x ≈ 0#) → ¬ ((x ⁻¹) ≈ 0#)
    x : {x y : A} → F x → F y → ((x * y) ⁻¹) ≈ ((y ⁻¹) * (x ⁻¹))

  _*-close\[0]_ : Closed₂ (F \[ _≈ 0# ]) _*_
  (x∈F , x≉0) *-close\[0] (y∈F , y≉0)
    = (x∈F *-close y∈F , noNonzeroZeroDivisors x∈F y∈F x≉0 y≉0)

  *-isMagma\[0] : IsMagma (F \[ _≈ 0# ]) _*_
  *-isMagma\[0] = record
    { isSet     = isSet\[0]
    ; _∙-close_ = _*-close\[0]_
    }

  *-assoc\[0] : Associative (F \[ _≈ 0# ]) _*_
  *-assoc\[0] (x∈F , _) (y∈F , _) (z∈F , _) = *-assoc x∈F y∈F z∈F

  *-isSemigroup\[0] : IsSemigroup (F \[ _≈ 0# ]) _*_
  *-isSemigroup\[0] = record
    { isMagma = *-isMagma\[0]
    ; ∙-assoc = *-assoc\[0]
    }

  1-identityˡ\[0] : LeftIdentity (F \[ _≈ 0# ]) _*_ 1#
  1-identityˡ\[0] (x∈F , _) = 1-identityˡ x∈F

  _1-identityʳ\[0] : RightIdentity (F \[ _≈ 0# ]) _*_ 1#
  _1-identityʳ\[0] (x∈F , _) = x∈F 1-identityʳ

  *-isMonoid\[0] : IsMonoid (F \[ _≈ 0# ]) _*_ 1#
  *-isMonoid\[0] = record
    { isSemigroup = *-isSemigroup\[0]
    ; ε-close     = (1-close , 1≉0)
    ; ε-identity  = (1-identityˡ\[0] , _1-identityʳ\[0])
    }

  *-isGroup\[0] : IsGroup (F \[ _≈ 0# ]) _*_ 1# _⁻¹
  *-isGroup\[0] = record
    { isMonoid = *-isMonoid\[0]
    ; _⁻¹-close    = _⁻¹-close\[0]
    ; _⁻¹-inverse  = _⁻¹-inverse\[0]
    }

  _*-comm\[0]_ : Commutative (F \[ _≈ 0# ]) _*_
  _*-comm\[0]_ (x∈F , _ ) (y∈F , _ ) = x∈F *-comm y∈F

  *-isAbelianGroup\[0] : IsAbelianGroup (F \[ _≈ 0# ]) _*_ 1# _⁻¹
  *-isAbelianGroup\[0] = record
    { isGroup    = *-isGroup\[0]
    ; _∙-comm_   = _*-comm\[0]_
    }
