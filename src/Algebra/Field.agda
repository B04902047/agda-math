
module Algebra.Field {A : Set} (_≈_ : A → A → Set) where

open import Algebra.DivisionRing _≈_ public

open import Basic.Logic
open import Basic.Properties _≈_
open import Basic.Subtype

record IsField
      (F : A → Set) (_+_ _*_ : A → A → A)
      (0# 1# : A) (- _⁻¹ : A → A) : Set₁ where
  field
    isDivisionRing : IsDivisionRing F _+_ _*_ 0# 1# - _⁻¹
    _*-comm_       : Commutative F _*_
    1≉0           : ¬ (1# ≈ 0#)

  open IsDivisionRing isDivisionRing
    renaming (
      1∈R to 1∈F
    ; 0∈R to 0∈F
    ) public

  private
    _+'_ : Closed₂ F _+_
    _+'_ = _+-close_
    _*'_ : Closed₂ F _*_
    _*'_ = _*-close_
    -' : Closed₁ F -
    -' = -‿close

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
          ∎⟨ 0∈F ⟩
          where
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

  prop-ix' : {x : A} → F x → ¬ (x ≈ 0#) → ¬ ((x ⁻¹) ≈ 0#)
  prop-ix' {x} x∈F x≉0 x⁻¹≈0 = 1≉0 1≈0
    where 1≈0 = begin
                1#
              ≈˘⟨ 1∈F , (x∈F , x≉0) ⁻¹-inverse\[0]ʳ ⟩
                x * (x ⁻¹)
              ≈⟨ x∈F *-close (proj₁ ((x∈F , x≉0) ⁻¹-close\[0])) , *-congʳ (proj₁ ((x∈F , x≉0) ⁻¹-close\[0])) 0∈F x∈F x⁻¹≈0 ⟩
                x * 0#
              ≈⟨ x∈F *-close 0∈F , x∈F 0-zeroʳ ⟩
                0#
              ∎⟨ 0∈F ⟩


  *-‿cancel : {x y : A} → F x → F y → ((- x) * (- y)) ≈ (x * y)
  *-‿cancel {x} {y} x' y'
    = begin
      (- x) * (- y)
    ≈⟨ -' x' *' -' y' , -‿assoc x' (-' y') ⟩
      - (x * (- y))
    ≈⟨ -' (x' *' (-' y')) , -‿cong (x' *' (-' y')) ((-' y') *' x') (x' *-comm (-' y')) ⟩
      - ((- y) * x)
    ≈⟨ -' ((-' y') *' x') , -‿cong ((-' y') *' x') (-' (y' *' x')) (-‿assoc y' x') ⟩
      - (- (y * x))
    ≈⟨ -' (-' (y' *' x')) , -‿doubleInverse (y' *' x') ⟩
      y * x
    ≈⟨ y' *' x' , y' *-comm x' ⟩
      x * y
    ∎⟨ x' *' y' ⟩


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
    ; ε∈M     = (1∈F , 1≉0)
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
