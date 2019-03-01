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

  *-cancel\[0]ˡ : {x y z : A} → R x → R y → (R\[ 0# ]) z
              →  (z * x) ≈ (z * y) → x ≈ y
  *-cancel\[0]ˡ {x} {y} {z} x∈R y∈R (z∈R , z!≈0) z*x≈z*y
    = begin
      x
    ≈˘⟨ x∈R , 1-identityˡ x∈R ⟩
      1# * x
    ≈˘⟨ 1-close *-close x∈R , *-congˡ (z⁻¹∈R *-close z∈R) 1-close x∈R ((z∈R , z!≈0) ⁻¹-inverseˡ) ⟩
      ((z ⁻¹) * z) * x
    ≈⟨ (z⁻¹∈R *-close z∈R) *-close x∈R , *-assoc z⁻¹∈R z∈R x∈R ⟩
      (z ⁻¹) * (z * x)
    ≈⟨ z⁻¹∈R *-close (z∈R *-close x∈R) , *-congʳ (z∈R *-close x∈R) (z∈R *-close y∈R) z⁻¹∈R z*x≈z*y ⟩
      (z ⁻¹) * (z * y)
    ≈˘⟨ z⁻¹∈R *-close (z∈R *-close y∈R) , *-assoc z⁻¹∈R z∈R y∈R ⟩
      ((z ⁻¹) * z) * y
    ≈⟨ (z⁻¹∈R *-close z∈R) *-close y∈R , *-congˡ (z⁻¹∈R *-close z∈R) 1-close y∈R ((z∈R , z!≈0) ⁻¹-inverseˡ) ⟩
      1# * y
    ≈⟨ 1-close *-close y∈R , 1-identityˡ y∈R ⟩
      y
    ∎⟨ y∈R ⟩
    where
      z⁻¹∈R = proj₁ ((z∈R , z!≈0) ⁻¹-close)
      z⁻¹!≈0 = proj₂ ((z∈R , z!≈0) ⁻¹-close)

  *-cancel\[0]ʳ : {x y z : A} → R x → R y → (R\[ 0# ]) z
              →  (x * z) ≈ (y * z) → x ≈ y
  *-cancel\[0]ʳ {x} {y} {z} x∈R y∈R (z∈R , z!≈0) x*z≈y*z
    = begin
      x
    ≈˘⟨ x∈R , x∈R 1-identityʳ ⟩
      x * 1#
    ≈˘⟨ x∈R *-close 1-close , *-congʳ (z∈R *-close z⁻¹∈R) 1-close x∈R ((z∈R , z!≈0) ⁻¹-inverseʳ) ⟩
      x * (z * (z ⁻¹))
    ≈˘⟨ x∈R *-close (z∈R *-close z⁻¹∈R) , *-assoc x∈R z∈R z⁻¹∈R ⟩
      (x * z) * (z ⁻¹)
    ≈⟨ (x∈R *-close z∈R) *-close z⁻¹∈R , *-congˡ (x∈R *-close z∈R) (y∈R *-close z∈R) z⁻¹∈R x*z≈y*z ⟩
      (y * z) * (z ⁻¹)
    ≈⟨ (y∈R *-close z∈R) *-close z⁻¹∈R , *-assoc y∈R z∈R z⁻¹∈R ⟩
      y * (z * (z ⁻¹))
    ≈⟨ y∈R *-close (z∈R *-close z⁻¹∈R) , *-congʳ (z∈R *-close z⁻¹∈R) 1-close y∈R ((z∈R , z!≈0) ⁻¹-inverseʳ) ⟩
      y * 1#
    ≈⟨ y∈R *-close 1-close , y∈R 1-identityʳ ⟩
      y
    ∎⟨ y∈R ⟩
    where
      z⁻¹∈R = proj₁ ((z∈R , z!≈0) ⁻¹-close)
      z⁻¹!≈0 = proj₂ ((z∈R , z!≈0) ⁻¹-close)
