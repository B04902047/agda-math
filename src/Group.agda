
module Algebra.Group
        {A : Set} (_≈_ : A → A → Set) where

open import Algebra.Monoid _≈_ public

open import Basic.Logic
open import Basic.Properties _≈_
open import Basic.Subtype

record IsGroup (G : A → Set) (_∙_ : A → A → A)
                (ε : A) (_⁻¹ : A → A) : Set₁ where
  field
    isMonoid    : IsMonoid G _∙_ ε
    _⁻¹-close   : Closed₁ G _⁻¹
    _⁻¹-inverse : Inverse G _∙_ ε _⁻¹

  open IsMonoid isMonoid public
    renaming (ε∈M to ε∈G)

  private
    _∙'_ : Closed₂ G _∙_
    _∙'_ = _∙-close_
    _⁻¹' : Closed₁ G _⁻¹
    _⁻¹' = _⁻¹-close
    ε' : G ε
    ε' = ε∈G

  ⁻¹-cong : Congruent₁ G _⁻¹
  ⁻¹-cong = ap _⁻¹

  _⁻¹-inverseˡ : {x : A} → G x → ((x ⁻¹) ∙ x) ≈ ε
  x∈G ⁻¹-inverseˡ = proj₁ (x∈G ⁻¹-inverse)

  _⁻¹-inverseʳ : {x : A} → G x → (x ∙ (x ⁻¹)) ≈ ε
  x∈G ⁻¹-inverseʳ = proj₂ (x∈G ⁻¹-inverse)

  ∙-cancelˡ : {x y z : A} → G x → G y → G z
              → (z ∙ x) ≈ (z ∙ y) → x ≈ y
  ∙-cancelˡ {x} {y} {z} x∈G y∈G z∈G z∙x≈z∙y
    = begin
      x
    ≈˘⟨ x∈G , ε-identityˡ x∈G ⟩
      ε ∙ x
    ≈˘⟨ ε∈G ∙-close x∈G , ∙-congˡ (z⁻¹∈G ∙-close z∈G) ε∈G x∈G (z∈G ⁻¹-inverseˡ) ⟩
      ((z ⁻¹) ∙ z) ∙ x
    ≈⟨ (z⁻¹∈G ∙-close z∈G) ∙-close x∈G , ∙-assoc z⁻¹∈G z∈G x∈G ⟩
      (z ⁻¹) ∙ (z ∙ x)
    ≈⟨ z⁻¹∈G ∙-close (z∈G ∙-close x∈G) , ∙-congʳ (z∈G ∙-close x∈G) (z∈G ∙-close y∈G) z⁻¹∈G z∙x≈z∙y ⟩
      (z ⁻¹) ∙ (z ∙ y)
    ≈˘⟨ z⁻¹∈G ∙-close (z∈G ∙-close y∈G) , ∙-assoc z⁻¹∈G z∈G y∈G ⟩
      ((z ⁻¹) ∙ z) ∙ y
    ≈⟨ (z⁻¹∈G ∙-close z∈G) ∙-close y∈G , ∙-congˡ (z⁻¹∈G ∙-close z∈G) ε∈G y∈G (z∈G ⁻¹-inverseˡ) ⟩
      ε ∙ y
    ≈⟨ ε∈G ∙-close y∈G , ε-identityˡ y∈G ⟩
      y
    ∎⟨ y∈G ⟩
    where z⁻¹∈G = z∈G ⁻¹-close

  ∙-cancelʳ : {x y z : A} → G x → G y → G z
              →  (x ∙ z) ≈ (y ∙ z) → x ≈ y
  ∙-cancelʳ {x} {y} {z} x∈G y∈G z∈G x∙z≈y∙z
    = begin
      x
    ≈˘⟨ x∈G , x∈G ε-identityʳ ⟩
      x ∙ ε
    ≈˘⟨ x∈G ∙-close ε∈G , ∙-congʳ (z∈G ∙-close z⁻¹∈G) ε∈G x∈G (z∈G ⁻¹-inverseʳ) ⟩
      x ∙ (z ∙ (z ⁻¹))
    ≈˘⟨ x∈G ∙-close (z∈G ∙-close z⁻¹∈G) , ∙-assoc x∈G z∈G z⁻¹∈G ⟩
      (x ∙ z) ∙ (z ⁻¹)
    ≈⟨ (x∈G ∙-close z∈G) ∙-close z⁻¹∈G , ∙-congˡ (x∈G ∙-close z∈G) (y∈G ∙-close z∈G) z⁻¹∈G x∙z≈y∙z ⟩
      (y ∙ z) ∙ (z ⁻¹)
    ≈⟨ (y∈G ∙-close z∈G) ∙-close z⁻¹∈G , ∙-assoc y∈G z∈G z⁻¹∈G ⟩
      y ∙ (z ∙ (z ⁻¹))
    ≈⟨ y∈G ∙-close (z∈G ∙-close z⁻¹∈G) , ∙-congʳ (z∈G ∙-close z⁻¹∈G) ε∈G y∈G (z∈G ⁻¹-inverseʳ) ⟩
      y ∙ ε
    ≈⟨ y∈G ∙-close ε∈G , y∈G ε-identityʳ ⟩
      y
    ∎⟨ y∈G ⟩
    where z⁻¹∈G = z∈G ⁻¹-close

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
      where y⁻¹∈G = y∈G ⁻¹-close

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
      where x⁻¹∈G = x∈G ⁻¹-close

  ⁻¹-doubleInverse : {x : A} → G x → ((x ⁻¹) ⁻¹) ≈ x
  ⁻¹-doubleInverse x∈G = sym x∈G ((x∈G ⁻¹-close) ⁻¹-close) (⁻¹-uniqueˡ x∈G (x∈G ⁻¹-close) (x∈G ⁻¹-inverseʳ))

  ∙⁻¹-distrib : {x y : A} → G x → G y → ((x ∙ y) ⁻¹) ≈ ((y ⁻¹) ∙ (x ⁻¹))
  ∙⁻¹-distrib {x} {y} x' y' = sym y⁻¹x⁻¹' (xy' ⁻¹-close) (⁻¹-uniqueʳ xy' y⁻¹x⁻¹' xyy⁻¹x⁻¹≈ε)
    where x⁻¹' = x' ⁻¹'
          y⁻¹' = y' ⁻¹'
          xy' = x' ∙' y'
          y⁻¹x⁻¹' = y⁻¹' ∙' x⁻¹'
          xyy⁻¹x⁻¹≈ε = begin
                        (x ∙ y) ∙ ((y ⁻¹) ∙ (x ⁻¹))
                      ≈˘⟨ xy' ∙' y⁻¹x⁻¹' , ∙-assoc xy' y⁻¹' x⁻¹' ⟩
                        ((x ∙ y) ∙ (y ⁻¹)) ∙ (x ⁻¹)
                      ≈⟨ (xy' ∙' y⁻¹') ∙' x⁻¹' , ∙-congˡ (xy' ∙' y⁻¹') (x' ∙' (y' ∙' y⁻¹')) x⁻¹' (∙-assoc x' y' y⁻¹') ⟩
                        (x ∙ (y ∙ (y ⁻¹))) ∙ (x ⁻¹)
                      ≈⟨ (x' ∙' (y' ∙' y⁻¹')) ∙' x⁻¹' , ∙-congˡ (x' ∙' (y' ∙' y⁻¹')) (x' ∙' ε') x⁻¹' (∙-congʳ (y' ∙' y⁻¹') ε' x' (y' ⁻¹-inverseʳ)) ⟩
                        (x ∙ ε) ∙ (x ⁻¹)
                      ≈⟨ (x' ∙' ε') ∙' x⁻¹' , ∙-congˡ (x' ∙' ε') x' x⁻¹' (x' ε-identityʳ) ⟩
                        x ∙ (x ⁻¹)
                      ≈⟨ x' ∙' x⁻¹' , x' ⁻¹-inverseʳ ⟩
                        ε
                      ∎⟨ ε' ⟩

  _/_ : A → A → A
  x / y = x ∙ (y ⁻¹)

  _/-close_ : Closed₂ G _/_
  x∈G /-close y∈G = x∈G ∙-close (y∈G ⁻¹-close)

  /-congˡ : LeftCongruent G _/_
  /-congˡ {x} {y} {z} x∈G y∈G z∈G x≈y
    = begin
        x / z
      ≈⟨ x∈G /-close z∈G , ∙-congˡ x∈G y∈G (z∈G ⁻¹-close) x≈y ⟩
        y / z
      ∎⟨ y∈G /-close z∈G ⟩

  /-congʳ : RightCongruent G _/_
  /-congʳ {x} {y} {z} x∈G y∈G z∈G x≈y
    = begin
        z / x
      ≈⟨ z∈G /-close x∈G , ∙-congʳ (x∈G ⁻¹-close) (y∈G ⁻¹-close) z∈G (⁻¹-cong x∈G y∈G x≈y) ⟩
        z / y
      ∎⟨ z∈G /-close y∈G ⟩

record _IsSubgroupOf_ (H G : A → Set) (∙ : A → A → A)
                      (ε : A) (⁻¹ : A → A) : Set₁ where
  field
    H⊆G       : H ⊆ G
    G-isGroup : IsGroup G ∙ ε ⁻¹
    H-isGroup : IsGroup H ∙ ε ⁻¹

record _IsSubgroupOf'_ (H G : A → Set) (_∙_ : A → A → A)
                       (ε : A) (_⁻¹ : A → A) : Set₁ where
  field
    H⊆G         : H ⊆ G
    G-isGroup   : IsGroup G _∙_ ε _⁻¹
    _∙-close-H_ : Closed₂ H _∙_
    ε∈G-H   : H ε
    _⁻¹-close-H : Closed₁ H _⁻¹

  open IsGroup G-isGroup renaming (isMonoid to G-isMonoid)

  H-isSubmonoidOf'-G : (H IsSubmonoidOf' G) _∙_ ε
  H-isSubmonoidOf'-G = record
    { N⊆M         = H⊆G
    ; M-isMonoid  = G-isMonoid
    ; ε∈M-N   = ε∈G-H
    ; _∙-close-N_ = _∙-close-H_
    }

  H-isMonoid : IsMonoid H _∙_ ε
  H-isMonoid = _IsSubmonoidOf'_.N-isMonoid H-isSubmonoidOf'-G

  _⁻¹-inverse-H : Inverse H _∙_ ε _⁻¹
  _⁻¹-inverse-H x∈H = (H⊆G x∈H) ⁻¹-inverse

  H-isGroup : IsGroup H _∙_ ε _⁻¹
  H-isGroup = record
    { isMonoid    = H-isMonoid
    ; _⁻¹-close   = _⁻¹-close-H
    ; _⁻¹-inverse = _⁻¹-inverse-H
    }

record IsAbelianGroup (G : A → Set) (∙ : A → A → A)
                      (ε : A) (⁻¹ : A → A) : Set₁ where
  field
    isGroup  : IsGroup G ∙ ε ⁻¹
    _∙-comm_ : Commutative G ∙

  open IsGroup isGroup public

  isCommutativeMonoid : IsCommutativeMonoid G ∙ ε
  isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; ε∈M         = ε∈G
    ; ε-identityˡ = ε-identityˡ
    ; _∙-comm_    = _∙-comm_
    }
