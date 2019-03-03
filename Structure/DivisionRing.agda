module Structure.DivisionRing
        {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ)where

open import Structure.Subtype

open import Structure.Properties _≈_
open import Structure.Ring _≈_ public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_; suc)


record IsDivisionRing (R : A → Set ℓ)
          (_+_ _*_ : A → A → A)
          (0# 1# : A) (- _⁻¹ : A → A) : Set (a ⊔ suc ℓ) where
  field
    isRing          : IsRing R _+_ _*_ 0# 1# -
    _⁻¹-close\[0]   : Closed₁ (R \[ _≈ 0# ]) _⁻¹
    _⁻¹-inverse\[0] : Inverse (R \[ _≈ 0# ]) _*_ 1# _⁻¹

  open IsRing isRing public

  R\[0]⊆R : (R \[ _≈ 0# ]) ⊆ R
  R\[0]⊆R (x∈R , _) = x∈R

  [0]-isSubsetoidOf-R : (R \[ _≈ 0# ]) IsSubsetoidOf R
  [0]-isSubsetoidOf-R = record
    { T⊆S        = R\[0]⊆R
    ; S-isSetoid = isSetoid
    }

  isSetoid\[0] : IsSetoid (R \[ _≈ 0# ])
  isSetoid\[0] = _IsSubsetoidOf_.T-isSetoid [0]-isSubsetoidOf-R

  ⁻¹-cong\[0] : Congruent₁ (R \[ _≈ 0# ]) _⁻¹
  ⁻¹-cong\[0] (x∈R , _) (y∈R , _) = ap _⁻¹ x∈R y∈R

  _⁻¹-inverse\[0]ˡ : LeftInverse (R \[ _≈ 0# ]) _*_ 1# _⁻¹
  (x∈R,x!≈0) ⁻¹-inverse\[0]ˡ  = proj₁ ((x∈R,x!≈0) ⁻¹-inverse\[0])

  _⁻¹-inverse\[0]ʳ : RightInverse (R \[ _≈ 0# ]) _*_ 1# _⁻¹
  (x∈R,x!≈0) ⁻¹-inverse\[0]ʳ  = proj₂ ((x∈R,x!≈0) ⁻¹-inverse\[0])

  *-cancel\[0]ˡ : {x y z : A} → R x → R y → (R \[ _≈ 0# ]) z
              →  (z * x) ≈ (z * y) → x ≈ y
  *-cancel\[0]ˡ {x} {y} {z} x∈R y∈R (z∈R , z!≈0) z*x≈z*y
    = begin
      x
    ≈˘⟨ x∈R , 1-identityˡ x∈R ⟩
      1# * x
    ≈˘⟨ 1-close *-close x∈R , *-congˡ (z⁻¹∈R *-close z∈R) 1-close x∈R ((z∈R , z!≈0) ⁻¹-inverse\[0]ˡ) ⟩
      ((z ⁻¹) * z) * x
    ≈⟨ (z⁻¹∈R *-close z∈R) *-close x∈R , *-assoc z⁻¹∈R z∈R x∈R ⟩
      (z ⁻¹) * (z * x)
    ≈⟨ z⁻¹∈R *-close (z∈R *-close x∈R) , *-congʳ (z∈R *-close x∈R) (z∈R *-close y∈R) z⁻¹∈R z*x≈z*y ⟩
      (z ⁻¹) * (z * y)
    ≈˘⟨ z⁻¹∈R *-close (z∈R *-close y∈R) , *-assoc z⁻¹∈R z∈R y∈R ⟩
      ((z ⁻¹) * z) * y
    ≈⟨ (z⁻¹∈R *-close z∈R) *-close y∈R , *-congˡ (z⁻¹∈R *-close z∈R) 1-close y∈R ((z∈R , z!≈0) ⁻¹-inverse\[0]ˡ) ⟩
      1# * y
    ≈⟨ 1-close *-close y∈R , 1-identityˡ y∈R ⟩
      y
    ∎⟨ y∈R ⟩
    where
      z⁻¹∈R = proj₁ ((z∈R , z!≈0) ⁻¹-close\[0])
      z⁻¹!≈0 = proj₂ ((z∈R , z!≈0) ⁻¹-close\[0])

  *-cancel\[0]ʳ : {x y z : A} → R x → R y → (R \[ _≈ 0# ]) z
              →  (x * z) ≈ (y * z) → x ≈ y
  *-cancel\[0]ʳ {x} {y} {z} x∈R y∈R (z∈R , z!≈0) x*z≈y*z
    = begin
      x
    ≈˘⟨ x∈R , x∈R 1-identityʳ ⟩
      x * 1#
    ≈˘⟨ x∈R *-close 1-close , *-congʳ (z∈R *-close z⁻¹∈R) 1-close x∈R ((z∈R , z!≈0) ⁻¹-inverse\[0]ʳ) ⟩
      x * (z * (z ⁻¹))
    ≈˘⟨ x∈R *-close (z∈R *-close z⁻¹∈R) , *-assoc x∈R z∈R z⁻¹∈R ⟩
      (x * z) * (z ⁻¹)
    ≈⟨ (x∈R *-close z∈R) *-close z⁻¹∈R , *-congˡ (x∈R *-close z∈R) (y∈R *-close z∈R) z⁻¹∈R x*z≈y*z ⟩
      (y * z) * (z ⁻¹)
    ≈⟨ (y∈R *-close z∈R) *-close z⁻¹∈R , *-assoc y∈R z∈R z⁻¹∈R ⟩
      y * (z * (z ⁻¹))
    ≈⟨ y∈R *-close (z∈R *-close z⁻¹∈R) , *-congʳ (z∈R *-close z⁻¹∈R) 1-close y∈R ((z∈R , z!≈0) ⁻¹-inverse\[0]ʳ) ⟩
      y * 1#
    ≈⟨ y∈R *-close 1-close , y∈R 1-identityʳ ⟩
      y
    ∎⟨ y∈R ⟩
    where
      z⁻¹∈R = proj₁ ((z∈R , z!≈0) ⁻¹-close\[0])
      z⁻¹!≈0 = proj₂ ((z∈R , z!≈0) ⁻¹-close\[0])

  *-congˡ\[0] : LeftCongruent (R \[ _≈ 0# ]) _*_
  *-congˡ\[0] {x} {y} {z} (x∈R , _) (y∈R , _) _
              = ap (_* z) x∈R y∈R

  *-congʳ\[0] : RightCongruent (R \[ _≈ 0# ]) _*_
  *-congʳ\[0] {x} {y} {z} (x∈R , _) (y∈R , _) _
              = ap (z *_) x∈R y∈R

  _/_ : A → A → A
  x / y = x * (y ⁻¹)

  _/-close\[0]_ : {x y : A} → R x → (R \[ _≈ 0# ]) y → R (x / y)
  x∈R /-close\[0] (y∈R,y!≈0) = x∈R *-close (proj₁ ((y∈R,y!≈0) ⁻¹-close\[0]))

  /-cong\[0]ˡ : {x y z : A} → R x → R y → (R \[ _≈ 0# ]) z → x ≈ y → (x / z) ≈ (y / z)
  /-cong\[0]ˡ {x} {y} {z} x∈R y∈R (z∈R,z!≈0) x≈y
    = begin
        x / z
      ≈⟨ x∈R /-close\[0] (z∈R,z!≈0) , *-congˡ x∈R y∈R (proj₁ ((z∈R,z!≈0) ⁻¹-close\[0])) x≈y ⟩
        y / z
      ∎⟨ y∈R /-close\[0] (z∈R,z!≈0) ⟩

  /-cong\[0]ʳ : {x y z : A} → (R \[ _≈ 0# ]) x → (R \[ _≈ 0# ]) y → R z → x ≈ y → (z / x) ≈ (z / y)
  /-cong\[0]ʳ {x} {y} {z} (x∈R,x!≈0) (y∈R,y!≈0) z∈R x≈y
    = begin
        z / x
      ≈⟨ z∈R /-close\[0] (x∈R,x!≈0) , *-congʳ (proj₁ ((x∈R,x!≈0) ⁻¹-close\[0])) (proj₁ ((y∈R,y!≈0) ⁻¹-close\[0])) z∈R (⁻¹-cong\[0] (x∈R,x!≈0) (y∈R,y!≈0) x≈y) ⟩
        z / y
      ∎⟨ z∈R /-close\[0] (y∈R,y!≈0) ⟩
