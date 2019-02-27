
module Field {a ℓ} {A : Set a}
        (F : A → Set ℓ) (_≈_ : A → A → Set ℓ) where

open import Properties _≈_
open import Ring _≈_ public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


F\[_] : A → A → Set ℓ
F\[ c ] x = (F x) × (¬ (x ≈ c))

record IsField (_+_ _*_ : A → A → A) (0# 1# : A) (-_ : A → A)
              (_⁻¹ : A → A) : Set (a ⊔ ℓ) where
  field
    isCommutativeRing : IsCommutativeRing F _+_ _*_ 0# 1# -_
    _⁻¹-close         : Closed₁ (F\[ 0# ]) _⁻¹
    ⁻¹-cong           : Congruent₁ (F\[ 0# ]) _⁻¹
    _⁻¹-inverse       : Inverse (F\[ 0# ]) _*_ 1# _⁻¹
    1!≈0              : ¬ (1# ≈ 0#)

  _⁻¹-inverseˡ : LeftInverse (F\[ 0# ]) _*_ 1# _⁻¹
  (x∈F,x!≈0) ⁻¹-inverseˡ  = proj₁ ((x∈F,x!≈0) ⁻¹-inverse)

  _⁻¹-inverseʳ : RightInverse (F\[ 0# ]) _*_ 1# _⁻¹
  (x∈F,x!≈0) ⁻¹-inverseʳ  = proj₂ ((x∈F,x!≈0) ⁻¹-inverse)

  open IsCommutativeRing F isCommutativeRing public

  noNonzeroZeroDivisors : {x y : A} → F x → F y
                        → ¬ (x ≈ 0#) → ¬ (y ≈ 0#)
                        → ¬ ((x * y) ≈ 0#)
  noNonzeroZeroDivisors {x} {y} x∈F y∈F x!≈0 y!≈0 x*y≈0
    = 1!≈0 1≈0
    where
      1≈0 = begin
            1#
          ≈˘⟨ 1∈F , 1∈F 1-identityʳ ⟩
            1# * 1#
          ≈˘⟨ 1∈F *-close 1∈F , *-congˡ x⁻¹*x∈F 1∈F 1∈F ((x∈F , x!≈0) ⁻¹-inverseˡ) ⟩
            ((x ⁻¹) * x) * 1#
          ≈˘⟨ x⁻¹*x∈F *-close 1∈F , *-congʳ (y∈F *-close y⁻¹∈F) 1∈F x⁻¹*x∈F ((y∈F , y!≈0) ⁻¹-inverseʳ) ⟩
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
            x⁻¹∈F = proj₁ ((x∈F , x!≈0) ⁻¹-close)
            x⁻¹!≈0 = proj₂ ((x∈F , x!≈0) ⁻¹-close)
            y⁻¹∈F = proj₁ ((y∈F , y!≈0) ⁻¹-close)
            y⁻¹!≈0 = proj₂ ((y∈F , y!≈0) ⁻¹-close)
            x⁻¹*x∈F = x⁻¹∈F *-close x∈F

  refl\[0] : Reflexive (F\[ 0# ])
  refl\[0] (x∈F , _) = refl x∈F

  sym\[0] : Symmetric (F\[ 0# ])
  sym\[0] (x∈F , _) (y∈F , _) = sym x∈F y∈F

  trans\[0] : Transitive (F\[ 0# ])
  trans\[0] (x∈F , _) (y∈F , _) (z∈F , _) = trans x∈F y∈F z∈F

  isEquivalence\[0] : IsEquivalence (F\[ 0# ])
  isEquivalence\[0] = record
    { refl  = refl\[0]
    ; sym   = sym\[0]
    ; trans = trans\[0]
    }

  isSetoid\[0] : IsSetoid (F\[ 0# ])
  isSetoid\[0] = record
    { isEquivalence = isEquivalence\[0]
    }

  _*-close\[0]_ : Closed₂ (F\[ 0# ]) _*_
  (x∈F , x!≈0) *-close\[0] (y∈F , y!≈0)
    = (x∈F *-close y∈F , noNonzeroZeroDivisors x∈F y∈F x!≈0 y!≈0)

  *-cong\[0] : Congruent₂ (F\[ 0# ]) _*_
  *-cong\[0] (x∈F , _ ) (y∈F , _ ) (u∈F , _ ) (v∈F , _ ) x≈y u≈v
    = *-cong x∈F y∈F u∈F v∈F x≈y u≈v

  *-congˡ\[0] : LeftCongruent (F\[ 0# ]) _*_
  *-congˡ\[0] = getLeftCongruent (F\[ 0# ]) refl\[0] *-cong\[0]

  *-congʳ\[0] : RightCongruent (F\[ 0# ]) _*_
  *-congʳ\[0] = getRightCongruent (F\[ 0# ]) refl\[0] *-cong\[0]

  *-isMagma\[0] : IsMagma (F\[ 0# ]) _*_
  *-isMagma\[0] = record
    { isSetoid  = isSetoid\[0]
    ; _∙-close_ = _*-close\[0]_
    ; ∙-cong    = *-cong\[0]
    }

  *-assoc\[0] : Associative (F\[ 0# ]) _*_
  *-assoc\[0] (x∈F , _) (y∈F , _) (z∈F , _) = *-assoc x∈F y∈F z∈F

  *-isSemigroup\[0] : IsSemigroup (F\[ 0# ]) _*_
  *-isSemigroup\[0] = record
    { isMagma = *-isMagma\[0]
    ; ∙-assoc = *-assoc\[0]
    }

  1-identityˡ\[0] : LeftIdentity (F\[ 0# ]) _*_ 1#
  1-identityˡ\[0] (x∈F , _) = 1-identityˡ x∈F

  _1-identityʳ\[0] : RightIdentity (F\[ 0# ]) _*_ 1#
  _1-identityʳ\[0] (x∈F , _) = x∈F 1-identityʳ

  *-isMonoid\[0] : IsMonoid (F\[ 0# ]) _*_ 1#
  *-isMonoid\[0] = record
    { isSemigroup = *-isSemigroup\[0]
    ; ε-close     = (1-close , 1!≈0)
    ; ε-identity  = (1-identityˡ\[0] , _1-identityʳ\[0])
    }

  *-isGroup\[0] : IsGroup (F\[ 0# ]) _*_ 1# _⁻¹
  *-isGroup\[0] = record
    { isMonoid = *-isMonoid\[0]
    ; _⁻¹-close    = _⁻¹-close
    ; ⁻¹-cong      = ⁻¹-cong
    ; _⁻¹-inverse  = _⁻¹-inverse
    }

  *-comm\[0] : Commutative (F\[ 0# ]) _*_
  *-comm\[0] (x∈F , _ ) (y∈F , _ ) = *-comm x∈F y∈F

  *-isAbelianGroup : IsAbelianGroup (F\[ 0# ]) _*_ 1# _⁻¹
  *-isAbelianGroup = record
    { isGroup = *-isGroup\[0]
    ; ∙-comm   = *-comm\[0]
    }

  -- isDivisionRing
  -- isIntegralDomain
