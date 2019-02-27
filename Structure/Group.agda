
module Group {a ℓ} {A : Set a}
        (_≈_ : A → A → Set ℓ) (G : A → Set ℓ) where

open import Properties _≈_ G
open import Monoid _≈_ G public

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


record IsGroup (_∙_ : A → A → A) (ε : A) (_⁻¹ : A → A) : Set (a ⊔ ℓ) where
  field
    isMonoid   : IsMonoid _∙_ ε
    _⁻¹-close : Closed₁ _⁻¹
    ⁻¹-cong    : Congruent₁ _⁻¹
    _⁻¹-inverse : Inverse _∙_ ε _⁻¹

  open IsMonoid isMonoid public

  _⁻¹-inverseˡ : {x : A} → G x → ((x ⁻¹) ∙ x) ≈ ε
  x∈G ⁻¹-inverseˡ = proj₁ (x∈G ⁻¹-inverse)

  _⁻¹-inverseʳ : {x : A} → G x → (x ∙ (x ⁻¹)) ≈ ε
  x∈G ⁻¹-inverseʳ = proj₂ (x∈G ⁻¹-inverse)

  ⁻¹-uniqueˡ : {x y : A} → G x → G y → (x ∙ y) ≈ ε → x ≈ (y ⁻¹)
  ⁻¹-uniqueˡ {x} {y} x∈G y∈G x∙y≈ε
    = begin
        x
      ≈˘⟨ x∈G , x∈G ε-identityʳ ⟩
        x ∙ ε
      ≈⟨ x∈G ∙-close ε∈G , ∙-congʳ ε∈G (y∈G ∙-close y⁻¹∈G) x∈G (sym (y∈G ∙-close y⁻¹∈G) ε∈G (y∈G ⁻¹-inverseʳ)) ⟩
        x ∙ (y ∙ (y ⁻¹))
      ≈˘⟨ x∈G ∙-close (y∈G ∙-close y⁻¹∈G) , ∙-assoc x∈G y∈G y⁻¹∈G ⟩
        (x ∙ y) ∙ (y ⁻¹)
      ≈⟨ (x∈G ∙-close y∈G) ∙-close y⁻¹∈G , ∙-congˡ (x∈G ∙-close y∈G) ε∈G y⁻¹∈G x∙y≈ε ⟩
        ε ∙ (y ⁻¹)
      ≈⟨ ε∈G ∙-close y⁻¹∈G , ε-identityˡ y⁻¹∈G ⟩
        (y ⁻¹)
      ∎⟨ y⁻¹∈G ⟩
      where ε∈G = ε-close
            y⁻¹∈G = y∈G ⁻¹-close

  ⁻¹-uniqueʳ : {x y : A} → G x → G y → (x ∙ y) ≈ ε → y ≈ (x ⁻¹)
  ⁻¹-uniqueʳ {x} {y} x∈G y∈G x∙y≈ε
    = begin
        y
      ≈˘⟨ y∈G , ε-identityˡ y∈G ⟩
        ε ∙ y
      ≈˘⟨ ε∈G ∙-close y∈G , ∙-congˡ (x⁻¹∈G ∙-close x∈G) ε∈G y∈G (x∈G ⁻¹-inverseˡ) ⟩
        ((x ⁻¹) ∙ x) ∙ y
      ≈⟨ (x⁻¹∈G ∙-close x∈G) ∙-close y∈G , ∙-assoc x⁻¹∈G x∈G  y∈G ⟩
        (x ⁻¹) ∙ (x ∙ y)
      ≈⟨ x⁻¹∈G ∙-close (x∈G ∙-close y∈G) , ∙-congʳ (x∈G ∙-close y∈G) ε∈G x⁻¹∈G x∙y≈ε ⟩
        (x ⁻¹) ∙ ε
      ≈⟨ x⁻¹∈G ∙-close ε∈G , x⁻¹∈G ε-identityʳ ⟩
        (x ⁻¹)
      ∎⟨ x⁻¹∈G ⟩
      where ε∈G = ε-close
            x⁻¹∈G = x∈G ⁻¹-close

  _/_ : A → A → A
  x / y = x ∙ (y ⁻¹)

  _/-close_ : Closed₂ _/_
  x∈G /-close y∈G = x∈G ∙-close (y∈G ⁻¹-close)

  /-congˡ : LeftCongruent _/_
  /-congˡ {x} {y} {z} x∈G y∈G z∈G x≈y
    = begin
        x / z
      ≈⟨ x∈G /-close z∈G , ∙-congˡ x∈G y∈G (z∈G ⁻¹-close) x≈y ⟩
        y / z
      ∎⟨ y∈G /-close z∈G ⟩

  /-congʳ : RightCongruent _/_
  /-congʳ {x} {y} {z} x∈G y∈G z∈G x≈y
    = begin
        z / x
      ≈⟨ z∈G /-close x∈G , ∙-congʳ (x∈G ⁻¹-close) (y∈G ⁻¹-close) z∈G (⁻¹-cong x∈G y∈G x≈y) ⟩
        z / y
      ∎⟨ z∈G /-close y∈G ⟩

record IsAbelianGroup (∙ : A → A → A)
                      (ε : A) (⁻¹ : A → A) : Set (a ⊔ ℓ) where
  field
    isGroup : IsGroup ∙ ε ⁻¹
    ∙-comm    : Commutative ∙

  open IsGroup isGroup public

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; ε-close     = ε-close
    ; ε-identityˡ = ε-identityˡ
    ; ∙-comm      = ∙-comm
    }
