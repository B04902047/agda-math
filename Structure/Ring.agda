
module Structure.Ring
        {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) where

open import Structure.Properties _≈_
open import Structure.Group _≈_ public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_; suc)

record IsRing (R : A → Set ℓ)
              (_+_ _*_ : A → A → A)
              (0# 1# : A) (-_ : A → A) : Set (a ⊔ suc ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup R _+_ 0# -_
    *-isMonoid       : IsMonoid R _*_ 1#
    distrib          : _DistributesOver_ R _*_ _+_

  distribˡ : _DistributesOverˡ_ R _*_ _+_
  distribˡ = proj₁ distrib

  distribʳ : _DistributesOverʳ_ R _*_ _+_
  distribʳ = proj₂ distrib

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( ∙-comm              to +-comm
    ; isGroup             to +-isGroup
    ;   _⁻¹-close         to -‿close
    ;   _⁻¹-inverse       to -‿inverse
    ;     _⁻¹-inverseˡ    to -‿inverseˡ
    ;     _⁻¹-inverseʳ    to -‿inverseʳ
    ;   ⁻¹-cong           to -‿cong
    ;     ⁻¹-uniqueˡ      to -‿uniqueˡ
    ;     ⁻¹-uniqueʳ      to -‿uniqueʳ
    ;     ∙-cancelˡ       to +-cancelˡ
    ;     ∙-cancelʳ       to +-cancelʳ
    ;     _/_             to _-_
    ;     _/-close_       to _-‿close_
    ;     /-congˡ         to -‿congˡ
    ;     /-congʳ         to -‿congʳ
    ;   isMonoid          to +-isMonoid
    ;     ε-close         to 0-close
    ;     ε-identity      to 0-identity
    ;       ε-identityˡ   to 0-identityˡ
    ;       _ε-identityʳ  to _0-identityʳ
    ;       ε-uniqueˡ     to 0-uniqueˡ
    ;       ε-uniqueʳ     to 0-uniqueʳ
    ;     isSemigroup     to +-isSemigroup
    ;       ∙-assoc       to +-assoc
    ;       isMagma       to +-isMagma
    ;         _∙-close_   to _+-close_
    ;         ∙-congˡ     to +-congˡ
    ;         ∙-congʳ     to +-congʳ
    ; isCommutativeMonoid to +-isCommutativeMonoid
    )

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( ε-close         to 1-close
    ; ε-identity      to 1-identity
    ;   ε-identityˡ   to 1-identityˡ
    ;   _ε-identityʳ  to _1-identityʳ
    ;   ε-uniqueˡ     to 1-uniqueˡ
    ;   ε-uniqueʳ     to 1-uniqueʳ
    ; isSemigroup     to *-isSemigroup
    ;   ∙-assoc       to *-assoc
    ;   isMagma       to *-isMagma
    ;     _∙-close_   to _*-close_
    ;     ∙-congˡ     to *-congˡ
    ;     ∙-congʳ     to *-congʳ
    )

  0-zeroˡ : LeftZero R _*_ 0#
  0-zeroˡ {x} x∈R =
    begin
      0# * x
    ≈˘⟨ 0*x∈R , 0*x∈R 0-identityʳ ⟩
      (0# * x) + 0#
    ≈˘⟨ 0*x∈R +-close 0∈R , +-congʳ (0*x∈R +-close -0*x∈R) 0∈R 0*x∈R (-‿inverseʳ 0*x∈R) ⟩
      (0# * x) + ((0# * x) - (0# * x))
    ≈˘⟨ 0*x∈R +-close (0*x∈R +-close -0*x∈R) , (+-assoc 0*x∈R 0*x∈R -0*x∈R) ⟩
      ((0# * x) + (0# * x)) - (0# * x)
    ≈˘⟨ (0*x∈R +-close 0*x∈R) +-close -0*x∈R , +-congˡ ((0∈R +-close 0∈R) *-close x∈R) (0*x∈R +-close 0*x∈R) -0*x∈R (distribʳ x∈R 0∈R 0∈R) ⟩
      ((0# + 0#) * x) - (0# * x)
    ≈⟨ ((0∈R +-close 0∈R) *-close x∈R) +-close -0*x∈R , +-congˡ ((0∈R +-close 0∈R) *-close x∈R) 0*x∈R -0*x∈R (*-congˡ (0∈R +-close 0∈R) 0∈R x∈R (0∈R 0-identityʳ)) ⟩
      (0# * x) - (0# * x)
    ≈⟨ 0*x∈R +-close -0*x∈R , -‿inverseʳ 0*x∈R ⟩
      0#
    ∎⟨ 0∈R ⟩
    where 0∈R    = 0-close
          0*x∈R  = 0∈R *-close x∈R
          -0*x∈R = -‿close 0*x∈R

  _0-zeroʳ : RightZero R _*_ 0#
  _0-zeroʳ {x} x∈R =
    begin
      x * 0#
    ≈˘⟨ x*0∈R , x*0∈R 0-identityʳ ⟩
      (x * 0#) + 0#
    ≈˘⟨ x*0∈R +-close 0∈R , +-congʳ (x*0∈R +-close -x*0∈R) 0∈R x*0∈R ((-‿inverseʳ x*0∈R)) ⟩
      (x * 0#) + ((x * 0#) - (x * 0#))
    ≈˘⟨ x*0∈R +-close (x*0∈R +-close -x*0∈R) , (+-assoc x*0∈R x*0∈R -x*0∈R) ⟩
      ((x * 0#) + (x * 0#)) - (x * 0#)
    ≈˘⟨ (x*0∈R +-close x*0∈R) +-close -x*0∈R , +-congˡ (x∈R *-close (0∈R +-close 0∈R)) (x*0∈R +-close x*0∈R) -x*0∈R (distribˡ x∈R 0∈R 0∈R) ⟩
      (x * (0# + 0#)) - (x * 0#)
    ≈⟨ (x∈R *-close (0∈R +-close 0∈R) ) +-close -x*0∈R , +-congˡ (x∈R *-close (0∈R +-close 0∈R) ) x*0∈R -x*0∈R (*-congʳ (0∈R +-close 0∈R) 0∈R x∈R (0-identityˡ 0∈R)) ⟩
      (x * 0#) - (x * 0#)
    ≈⟨ x*0∈R +-close -x*0∈R , -‿inverseʳ x*0∈R ⟩
      0#
    ∎⟨ 0∈R ⟩
    where 0∈R    = 0-close
          x*0∈R  = x∈R *-close 0∈R
          -x*0∈R = -‿close x*0∈R

  negativeUnit : {x : A} → R x → ((- 1#) * x) ≈ (- x)
  negativeUnit {x} x∈R
    = begin
      (- 1#) * x
    ≈˘⟨ -1*x∈R , -1*x∈R 0-identityʳ ⟩
      ((- 1#) * x) + 0#
    ≈˘⟨ -1*x∈R +-close 0∈R , +-congʳ (x∈R +-close -x∈R) 0∈R -1*x∈R (-‿inverseʳ x∈R) ⟩
      ((- 1#) * x) + (x - x)
    ≈˘⟨ -1*x∈R +-close (x∈R +-close -x∈R) , +-assoc -1*x∈R x∈R -x∈R ⟩
      (((- 1#) * x) + x) - x
    ≈˘⟨ (-1*x∈R +-close x∈R) +-close -x∈R , -‿congˡ (-1*x∈R +-close 1*x∈R) (-1*x∈R +-close x∈R) x∈R (+-congʳ 1*x∈R x∈R -1*x∈R (1-identityˡ x∈R)) ⟩
      (((- 1#) * x) + (1# * x)) - x
    ≈˘⟨ (-1*x∈R +-close 1*x∈R) +-close -x∈R , -‿congˡ ((-1∈R +-close 1∈R) *-close x∈R) (-1*x∈R +-close 1*x∈R) x∈R (distribʳ x∈R -1∈R 1∈R) ⟩
      (((- 1#) + 1#) * x) - x
    ≈⟨ ((-1∈R +-close 1∈R) *-close x∈R) +-close -x∈R , -‿congˡ ((-1∈R +-close 1∈R) *-close x∈R) (0∈R *-close x∈R) x∈R (*-congˡ (-1∈R +-close 1∈R) 0∈R x∈R (-‿inverseˡ 1∈R)) ⟩
      (0# * x) - x
    ≈⟨ (0∈R *-close x∈R) +-close -x∈R , -‿congˡ (0∈R *-close x∈R) 0∈R x∈R (0-zeroˡ x∈R) ⟩
      0# - x
    ≈⟨ 0∈R +-close -x∈R , 0-identityˡ -x∈R ⟩
      - x
    ∎⟨ -‿close x∈R ⟩
    where 0∈R = 0-close
          1∈R = 1-close
          -1∈R = -‿close 1-close
          -x∈R = -‿close x∈R
          1*x∈R = 1∈R *-close x∈R
          -1*x∈R = -1∈R *-close x∈R

  -- postulate
  --   zeroRing : (1# ≈ 0#) → (a : A) → (¬ (¬ (a ≈ 1#)))

record IsCommutativeRing (R : A → Set ℓ)
          (+ * : A → A → A)
          (0# 1# : A) (- : A → A) : Set (a ⊔ suc ℓ) where
  field
    isRing : IsRing R + * 0# 1# -
    *-comm : Commutative R *

  open IsRing isRing public

  *-isCommutativeMonoid : IsCommutativeMonoid R * 1#
  *-isCommutativeMonoid =  record
    { isSemigroup = *-isSemigroup
    ; ε-close     = 1-close
    ; ε-identityˡ = 1-identityˡ
    ; ∙-comm        = *-comm
    }

record IsIntegralDomain (R : A → Set ℓ)
          (_+_ _*_ : A → A → A)
          (0# 1# : A) (- : A → A) : Set (a ⊔ suc ℓ) where
  field
    isRing : IsRing R _+_ _*_ 0# 1# -
    noNonzeroZeroDivisors : {x y : A} → R x → R y
                          → ¬ (x ≈ 0#) → ¬ (y ≈ 0#)
                          → ¬ ((x * y) ≈ 0#)
  open IsRing isRing public
