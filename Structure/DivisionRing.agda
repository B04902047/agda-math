module Structure.DivisionRing {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) (R : A → Set ℓ) where

open import Structure.Substructure _≈_ R
  renaming (S\[_] to R\[_])

open import Structure.Properties _≈_
open import Structure.Ring _≈_ R public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


record IsDivisionRing (_+_ _*_ : A → A → A)
          (0# 1# : A) (- _⁻¹ : A → A) : Set (a ⊔ ℓ) where
  field
    isRing      : IsRing _+_ _*_ 0# 1# -
    _⁻¹-close   : Closed₁ (R\[ 0# ]) _⁻¹
    ⁻¹-cong     : Congruent₁ (R\[ 0# ]) _⁻¹
    _⁻¹-inverse : Inverse (R\[ 0# ]) _*_ 1# _⁻¹

  open IsRing isRing public

  _⁻¹-inverseˡ : LeftInverse (R\[ 0# ]) _*_ 1# _⁻¹
  (x∈R,x!≈0) ⁻¹-inverseˡ  = proj₁ ((x∈R,x!≈0) ⁻¹-inverse)

  _⁻¹-inverseʳ : RightInverse (R\[ 0# ]) _*_ 1# _⁻¹
  (x∈R,x!≈0) ⁻¹-inverseʳ  = proj₂ ((x∈R,x!≈0) ⁻¹-inverse)
