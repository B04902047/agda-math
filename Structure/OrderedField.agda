
module Structure.OrderedField {A : Set} (_≈_ : A → A → Set) where

open import Structure.OrderedSet _≈_
open import Structure.Field _≈_
open import Structure.Properties _≈_
open import Structure.Subtype

open import Data.List hiding ([_])
open import Data.Nat
  renaming
  ( ℕ to ℕ
  ; _≤_ to _≤ᴺ_
  ; _≥_ to _≥ᴺ_
  ; _<_ to _<ᴺ_
  ; _>_ to _>ᴺ_
  )
open import Structure.Number
  renaming
  (≤-trans to ≤ᴺ-trans)

open import Structure.Logic

record IsOrderedField
          (F : A → Set)
          (_+_ _*_ : A → A → A)
          (0# 1# : A) (- _⁻¹ : A → A)
          (_≤_ : A → A → Set) : Set₁ where
  field
    isField      : IsField F _+_ _*_ 0# 1# - _⁻¹
    isOrderedSet : IsOrderedSet F _≤_
    ≤+-compˡ     : {x y z : A} → F x → F y → F z
                  → x ≤ y → (x + z) ≤ (y + z)
    ≤*-comp      : {x y : A} → F x → F y
                  → 0# ≤ x → 0# ≤ y → 0# ≤ (x * y)
  open IsField isField hiding (_∎⟨_⟩; _≈⟨_,_⟩_; _≈˘⟨_,_⟩_; _≡⟨_⟩_; _≡˘⟨_⟩_; _≡⟨⟩_; begin_)
  open IsOrderedSet isOrderedSet

  ≤+-compʳ : {x y z : A} → F x → F y → F z
            → x ≤ y → (z + x) ≤ (z + y)
  ≤+-compʳ {x} {y} {z} x∈F y∈F z∈F x≤y
    = ≤-begin
      z + x
    ≈≤⟨ z∈F +-close x∈F , +-comm z∈F x∈F ⟩
      x + z
    ≤≈⟨ x∈F +-close z∈F , ≤+-compˡ x∈F y∈F z∈F x≤y ⟩
      y + z
    ≈⟨ y∈F +-close z∈F , +-comm y∈F z∈F ⟩
      z + y
    ∎⟨ z∈F +-close y∈F ⟩

  ≤-‿reverse : {x : A} → F x → x ≤ 0# → (- x) ≥ 0#
  ≤-‿reverse {x} x∈F x≤0
    = ≤-begin
      0#
    ≈≤˘⟨ 0-close , -‿inverseʳ x∈F ⟩
      x + (- x)
    ≤≈⟨ x∈F +-close -‿close x∈F , ≤+-compˡ x∈F 0-close (-‿close x∈F) x≤0 ⟩
      0# + (- x)
    ≈⟨ 0-close +-close -‿close x∈F , 0-identityˡ (-‿close x∈F) ⟩
      - x
    ∎⟨ -‿close x∈F ⟩
  ≥-‿reverse : {x : A} → F x → x ≥ 0# → (- x) ≤ 0#
  ≥-‿reverse {x} x∈F 0≤x
    = ≤-begin
      - x
    ≈≤˘⟨ -‿close x∈F , 0-identityˡ (-‿close x∈F) ⟩
      0# + (- x)
    ≤≈⟨ 0-close +-close -‿close x∈F , ≤+-compˡ 0-close x∈F (-‿close x∈F) 0≤x ⟩
      x + (- x)
    ≈⟨ x∈F +-close -‿close x∈F , -‿inverseʳ x∈F ⟩
      0#
    ∎⟨ 0-close ⟩

  prop-1-1-2-xi-1 : {x y z : A} → F x → F y → F z
                  → x ≤ y → 0# ≤ z → (x * z) ≤ (y * z)
  prop-1-1-2-xi-1 {x} {y} {z} x∈F y∈F z∈F x≤y 0≤z
    = ≤-begin
      x * z
    ≈≤˘⟨ x∈F *-close z∈F , 0-identityˡ (x∈F *-close z∈F) ⟩
      0# + (x * z)
    ≤≈⟨ 0-close +-close (x∈F *-close z∈F) , ≤+-compˡ 0-close ((y∈F *-close z∈F) +-close (-‿close (x∈F *-close z∈F))) (x∈F *-close z∈F) 0≤yz-xz ⟩
      ((y * z) + (- (x * z))) + (x * z)
    ≈⟨ ((y∈F *-close z∈F) +-close (-‿close (x∈F *-close z∈F))) +-close (x∈F *-close z∈F) , +-assoc (y∈F *-close z∈F) (-‿close (x∈F *-close z∈F)) (x∈F *-close z∈F) ⟩
      (y * z) + (- (x * z) + (x * z))
    ≈⟨ (y∈F *-close z∈F) +-close ((-‿close (x∈F *-close z∈F)) +-close (x∈F *-close z∈F)) , +-congʳ ((-‿close (x∈F *-close z∈F)) +-close (x∈F *-close z∈F)) 0-close (y∈F *-close z∈F) (-‿inverseˡ (x∈F *-close z∈F)) ⟩
      (y * z) + 0#
    ≈⟨ (y∈F *-close z∈F) +-close 0-close , (y∈F *-close z∈F) 0-identityʳ ⟩
      y * z
    ∎⟨ y∈F *-close z∈F ⟩
    where 0≤y-x = ≤-begin
                    0#
                  ≈≤˘⟨ 0-close , -‿inverseʳ x∈F ⟩
                    x + (- x)
                  ≤⟨ x∈F +-close (-‿close x∈F) , ≤+-compˡ x∈F y∈F (-‿close x∈F) x≤y ⟩
                    y + (- x)
                  ≤-∎⟨ y∈F +-close (-‿close x∈F) ⟩
          0≤yz-xz = ≤-begin
                    0#
                  ≤≈⟨ 0-close , ≤*-comp (y∈F +-close (-‿close (x∈F))) z∈F 0≤y-x 0≤z ⟩
                    ((y + (- x)) * z)
                  ≈⟨ (y∈F +-close (-‿close x∈F)) *-close z∈F , distribʳ z∈F y∈F (-‿close (x∈F)) ⟩
                    (y * z) + ((- x) * z)
                  ≈⟨ (y∈F *-close z∈F) +-close ((-‿close x∈F) *-close z∈F) , +-congʳ ((-‿close (x∈F)) *-close z∈F) (-‿close (x∈F *-close z∈F)) (y∈F *-close z∈F) (-‿assoc x∈F z∈F) ⟩
                    (y * z) + (- (x * z))
                  ∎⟨ (y∈F *-close z∈F) +-close (-‿close (x∈F *-close z∈F)) ⟩


  prop-1-1-2-xi-2 : {x y z : A} → F x → F y → F z
                  → x ≤ y → z ≤ 0# → (y * z) ≤ (x * z)
  prop-1-1-2-xi-2 {x} {y} {z} x∈F y∈F z∈F x≤y z≤0
    = ≤-begin
      y * z
    ≈≤˘⟨ y∈F *-close z∈F , (y∈F *-close z∈F) 0-identityʳ ⟩
      (y * z) + 0#
    ≈≤˘⟨ (y∈F *-close z∈F) +-close 0-close , +-congʳ ((-‿close (x∈F *-close z∈F)) +-close (x∈F *-close z∈F)) 0-close (y∈F *-close z∈F) (-‿inverseˡ (x∈F *-close z∈F)) ⟩
      (y * z) + ((- (x * z)) + (x * z))
    ≈≤˘⟨ (y∈F *-close z∈F) +-close ((-‿close (x∈F *-close z∈F)) +-close (x∈F *-close z∈F) ) , +-assoc (y∈F *-close z∈F) (-‿close (x∈F *-close z∈F)) (x∈F *-close z∈F) ⟩
      ((y * z) + (- (x * z))) + (x * z)
    ≤≈⟨ ((y∈F *-close z∈F) +-close (-‿close (x∈F *-close z∈F))) +-close (x∈F *-close z∈F) , ≤+-compˡ ((y∈F *-close z∈F) +-close (-‿close (x∈F *-close z∈F))) 0-close (x∈F *-close z∈F) yz-xz≤0 ⟩
      0# + (x * z)
    ≈⟨ 0-close +-close (x∈F *-close z∈F) , 0-identityˡ (x∈F *-close z∈F) ⟩
      x * z
    ∎⟨ x∈F *-close z∈F ⟩
    where -xz≤-yz = ≤-begin
                    - (x * z)
                  ≈≤⟨ -‿close (x∈F *-close z∈F) , -‿cong (x∈F *-close z∈F) (z∈F *-close x∈F) (*-comm x∈F z∈F) ⟩
                    - (z * x)
                  ≈≤˘⟨ -‿close (z∈F *-close x∈F) , -‿assoc z∈F x∈F ⟩
                    (- z) * x
                  ≈≤⟨ (-‿close z∈F) *-close x∈F , *-comm (-‿close z∈F) x∈F ⟩
                    x * (- z)
                  ≤≈⟨ x∈F *-close (-‿close z∈F) , prop-1-1-2-xi-1 x∈F y∈F (-‿close z∈F) x≤y (≤-‿reverse z∈F z≤0) ⟩
                    y * (- z)
                  ≈⟨ y∈F *-close (-‿close z∈F) , *-comm y∈F (-‿close z∈F) ⟩
                    (- z) * y
                  ≈⟨ (-‿close z∈F) *-close y∈F , -‿assoc z∈F y∈F ⟩
                    - (z * y)
                  ≈⟨ -‿close (z∈F *-close y∈F) , -‿cong (z∈F *-close y∈F) (y∈F *-close z∈F) (*-comm z∈F y∈F) ⟩
                    - (y * z)
                  ∎⟨ -‿close (y∈F *-close z∈F) ⟩
          yz-xz≤0 = ≤-begin
                    (y * z) + (- (x * z))
                  ≤≈⟨ (y∈F *-close z∈F) +-close (-‿close (x∈F *-close z∈F)) , ≤+-compʳ (-‿close (x∈F *-close z∈F)) (-‿close (y∈F *-close z∈F)) (y∈F *-close z∈F) -xz≤-yz ⟩
                    (y * z) + (- (y * z))
                  ≈⟨ (y∈F *-close z∈F) +-close (-‿close (y∈F *-close z∈F)) , -‿inverseʳ (y∈F *-close z∈F) ⟩
                    0#
                  ∎⟨ 0-close ⟩

  *-‿cancel : {x y : A} → F x → F y → ((- x) * (- y)) ≈ (x * y)
  *-‿cancel {x} {y} x∈F y∈F
    = begin
      (- x) * (- y)
    ≈⟨ -‿close x∈F *-close -‿close y∈F , -‿assoc x∈F (-‿close y∈F) ⟩
      - (x * (- y))
    ≈⟨ -‿close (x∈F *-close (-‿close y∈F)) , -‿cong (x∈F *-close (-‿close y∈F)) ((-‿close y∈F) *-close x∈F) (*-comm x∈F (-‿close y∈F)) ⟩
      - ((- y) * x)
    ≈⟨ -‿close ((-‿close y∈F) *-close x∈F) , -‿cong ((-‿close y∈F) *-close x∈F) (-‿close (y∈F *-close x∈F)) (-‿assoc y∈F x∈F) ⟩
      - (- (y * x))
    ≈⟨ -‿close (-‿close (y∈F *-close x∈F)) , -‿doubleInverse (y∈F *-close x∈F) ⟩
      y * x
    ≈⟨ y∈F *-close x∈F , *-comm y∈F x∈F ⟩
      x * y
    ∎⟨ x∈F *-close y∈F ⟩

  prop-1-1-2-xii-1 : {x y : A} → F x → F y
                  → x ≤ 0# → y ≤ 0# → 0# ≤ (x * y)
  prop-1-1-2-xii-1 {x} {y} x∈F y∈F x≤0 y≤0
    = ≤-begin
      0#
    ≤≈⟨ 0-close , ≤*-comp (-‿close x∈F) (-‿close y∈F) (≤-‿reverse x∈F x≤0) (≤-‿reverse y∈F y≤0) ⟩
      ((- x) * (- y))
    ≈⟨ (-‿close x∈F) *-close (-‿close y∈F) , *-‿cancel x∈F y∈F ⟩
      x * y
    ∎⟨ x∈F *-close y∈F ⟩

  prop-1-1-2-xii-2 : {x y : A} → F x → F y
                  → x ≤ 0# → y ≥ 0# → (x * y) ≤ 0#
  prop-1-1-2-xii-2 {x} {y} x∈F y∈F x≤0 y≥0
    = ≤-begin
      x * y
    ≈≤˘⟨ x∈F *-close y∈F , -‿doubleInverse (x∈F *-close y∈F) ⟩
      - (- (x * y))
    ≤≈⟨ -‿close (-‿close (x∈F *-close y∈F)) , ≥-‿reverse (-‿close (x∈F *-close y∈F)) -xy≥0 ⟩
      0#
    ∎⟨ 0-close ⟩
    where -xy≥0 = ≤-begin
                  0#
                ≤≈⟨ 0-close , prop-1-1-2-xii-1 x∈F (-‿close y∈F) x≤0 (≥-‿reverse y∈F y≥0) ⟩
                  x * (- y)
                ≈⟨ x∈F *-close (-‿close y∈F) , *-comm x∈F (-‿close y∈F) ⟩
                  (- y) * x
                ≈⟨ (-‿close y∈F) *-close x∈F , -‿assoc y∈F x∈F ⟩
                  - (y * x)
                ≈⟨ -‿close (y∈F *-close x∈F) , -‿cong (y∈F *-close x∈F) (x∈F *-close y∈F) (*-comm y∈F x∈F) ⟩
                  - (x * y)
                ∎⟨ -‿close (x∈F *-close y∈F) ⟩
  prop-1-1-2-xii-3 : {x y : A} → F x → F y
                  → x ≥ 0# → y ≤ 0# → (x * y) ≤ 0#
  prop-1-1-2-xii-3 {x} {y} x∈F y∈F x≥0 y≤0
    = ≤-begin
      x * y
    ≈≤⟨ x∈F *-close y∈F , *-comm x∈F y∈F ⟩
      y * x
    ≤≈⟨ y∈F *-close x∈F , (prop-1-1-2-xii-2 y∈F x∈F y≤0 x≥0) ⟩
      0#
    ∎⟨ 0-close ⟩
  prop-1-1-2-xii-4 : {x y : A} → F x → F y
                      → x ≥ 0# → y ≥ 0# → (x * y) ≥ 0#
  prop-1-1-2-xii-4 {x} {y} x∈F y∈F x≥0 y≥0
      = ≤-begin
        0#
      ≈≤˘⟨ 0-close , 0-zeroˡ y∈F ⟩
        0# * y
      ≤⟨ 0-close *-close y∈F , prop-1-1-2-xi-1 0-close x∈F y∈F x≥0 y≥0 ⟩
        x * y
      ≤-∎⟨ x∈F *-close y∈F ⟩
  prop-1-1-2-xii-5 : {x y : A} → F x → F y
                      → x ≥ 0# → y ≥ 0# → (x + y) ≥ 0#
  prop-1-1-2-xii-5 {x} {y} x∈F y∈F x≥0 y≥0
      = ≤-begin
        0#
      ≈≤˘⟨ 0-close , 0-close 0-identityʳ ⟩
        0# + 0#
      ≤⟨ 0-close +-close 0-close , ≤+-compˡ 0-close x∈F 0-close x≥0 ⟩
        x + 0#
      ≤⟨ x∈F +-close 0-close , ≤+-compʳ 0-close y∈F x∈F y≥0 ⟩
        x + y
      ≤-∎⟨ x∈F +-close y∈F ⟩
  prop-1-1-2-xii-6 : {x y : A} → F x → F y
                      → x ≤ 0# → y ≤ 0# → (x + y) ≤ 0#
  prop-1-1-2-xii-6 {x} {y} x∈F y∈F x≤0 y≤0
      = ≤-begin
        x + y
      ≤⟨ x∈F +-close y∈F , ≤+-compʳ y∈F  0-close x∈F y≤0 ⟩
        x + 0#
      ≤≈⟨ x∈F +-close 0-close , ≤+-compˡ x∈F 0-close  0-close x≤0 ⟩
        0# + 0#
      ≈⟨ 0-close +-close 0-close , 0-close 0-identityʳ ⟩
        0#
      ∎⟨ 0-close ⟩


  sign : {x : A} → F x → (x ≥ 0# ⊎ x ≤ 0#)
  sign = ≤-connex 0-close

  prop-1-1-2-xiv : {x : A} → F x → 0# ≤ (x * x)
  prop-1-1-2-xiv {x} x∈F = [ (λ 0≤x → ≤*-comp x∈F x∈F 0≤x 0≤x) , (λ x≤0 → prop-1-1-2-xii-1 x∈F x∈F x≤0 x≤0) ] (sign x∈F)

  ∣_∣ : (x : A) → x ≥ 0# ⊎ x ≤ 0# → A
  ∣ x ∣ (inj₁ x≥0) = x
  ∣ x ∣ (inj₂ x≤0) = - x
-- def. problem
  -- abs : {x : A} → F x → A
  -- abs {x} x∈F = [ (λ _ → x) , (λ a → (- x)) ] (sign x∈F)
  --
  -- prop-1-1-5-i-1 : {x : A} → (x' : F x) → 0# ≤ abs x'
  -- prop-1-1-5-i-1 {x} x' = {!   !}
-- end. problem
  ∣_∣-close : {x : A} → F x → (x' : x ≥ 0# ⊎ x ≤ 0#)
              → F (∣ x ∣ x')
  ∣ x∈F ∣-close (inj₁ x≥0) = x∈F
  ∣ x∈F ∣-close (inj₂ x≤0) = -‿close x∈F

  prop-1-1-5-i : {x : A} → F x → (x' : x ≥ 0# ⊎ x ≤ 0#) → 0# ≤ ∣ x ∣ x'
  prop-1-1-5-i x∈F (inj₁ x≥0) = x≥0
  prop-1-1-5-i x∈F (inj₂ x≤0) = ≤-‿reverse x∈F x≤0

  lemma-1-1-5-ii-1 : {x : A} → F x → (x ≈ 0#) → (- x ≈ 0#)
  lemma-1-1-5-ii-1 {x} x∈F x≈0
    = begin
      - x
    ≈˘⟨ -‿close x∈F , 0-identityˡ (-‿close x∈F) ⟩
      0# + (- x)
    ≈˘⟨ 0-close +-close -‿close x∈F , +-congˡ x∈F 0-close (-‿close x∈F) x≈0 ⟩
      x + (- x)
    ≈⟨ x∈F +-close -‿close x∈F , -‿inverseʳ x∈F ⟩
      0#
    ∎⟨ 0-close ⟩

  lemma-1-1-5-ii-2 : {x : A} → F x → (- x ≈ 0#) → (x ≈ 0#)
  lemma-1-1-5-ii-2 {x} x∈F -x≈0
        = begin
          x
        ≈˘⟨ x∈F , -‿doubleInverse x∈F ⟩
          - (- x)
        ≈⟨ -‿close (-‿close x∈F) , lemma-1-1-5-ii-1 (-‿close x∈F) -x≈0 ⟩
          0#
        ∎⟨ 0-close ⟩

  prop-1-1-5-ii : {x : A} → F x → (sign : x ≥ 0# ⊎ x ≤ 0#)
                  → (∣ x ∣ sign ≈ 0#) ↔ (x ≈ 0#)
  prop-1-1-5-ii x∈F (inj₁ x≥0) = (id , id)
  prop-1-1-5-ii x∈F (inj₂ x≤0) = (lemma-1-1-5-ii-2 x∈F , lemma-1-1-5-ii-1 x∈F)

  ∣∣-cong : {x y : A} → F x → F y
              → (x' : x ≥ 0# ⊎ x ≤ 0#)
              → (y' : y ≥ 0# ⊎ y ≤ 0#)
              → x ≈ y
              → ∣ x ∣ x' ≈ ∣ y ∣ y'
  ∣∣-cong x∈F y∈F (inj₁ x≥0) (inj₁ y≥0) x≈y = x≈y
  ∣∣-cong {x} {y} x∈F y∈F (inj₁ x≥0) (inj₂ y≤0) x≈y
            = begin
              x
            ≈˘⟨ x∈F , proj₂ y≈0∧0≈x ⟩
              0#
            ≈˘⟨ 0-close , lemma-1-1-5-ii-1 y∈F (proj₁ y≈0∧0≈x) ⟩
              - y
            ∎⟨ -‿close y∈F ⟩
            where y≈0∧0≈x = ≤≈-sandwich y∈F x∈F 0-close y≤0 x≥0 (≈-sym x∈F y∈F x≈y)
  ∣∣-cong {x} {y} x∈F y∈F (inj₂ x≤0) (inj₁ y≥0) x≈y
            = begin
              - x
            ≈⟨ -‿close x∈F , lemma-1-1-5-ii-1 x∈F (proj₁ x≈0∧0≈y) ⟩
              0#
            ≈⟨ 0-close , proj₂ x≈0∧0≈y ⟩
              y
            ∎⟨ y∈F ⟩
            where x≈0∧0≈y = ≤≈-sandwich x∈F y∈F 0-close x≤0 y≥0 x≈y
  ∣∣-cong x∈F y∈F (inj₂ x≤0) (inj₂ y≤0) x≈y = -‿cong x∈F y∈F x≈y

  lemma-1-1-2-xiii : 1# ≤ 0# → 0# ≤ 1#
  lemma-1-1-2-xiii 1≤0 = ⊥-elim false
                        where -1≥0 = ≤-‿reverse 1-close 1≤0
                              1*-1≤0 = prop-1-1-2-xii-2 1-close (-‿close 1-close) 1≤0 -1≥0
                              -1≤0 = ≤-begin
                                      - 1#
                                    ≈≤˘⟨ -‿close 1-close , 1-identityˡ (-‿close 1-close) ⟩
                                      1# * (- 1#)
                                    ≤⟨ 1-close *-close -‿close 1-close , 1*-1≤0 ⟩
                                      0#
                                    ≤-∎⟨ 0-close ⟩
                              -1≈0 = ≤-anti-sym (-‿close 1-close) 0-close -1≤0 -1≥0
                              1≈0 = lemma-1-1-5-ii-2 1-close -1≈0
                              false = 1!≈0 1≈0
  1≥0 : 0# ≤ 1#
  1≥0 = [ id , lemma-1-1-2-xiii ] (sign 1-close)

  ≤-‿comp : {x y : A} → F x → F y → x ≤ y → - y ≤ - x
  ≤-‿comp {x} {y} x∈F y∈F x≤y = ≤-begin
                        - y
                      ≈≤˘⟨ -‿close y∈F , negativeUnit y∈F ⟩
                        (- 1#) * y
                      ≈≤⟨ -‿close 1-close *-close y∈F , *-comm (-‿close 1-close) y∈F ⟩
                        y * (- 1#)
                      ≤≈⟨ y∈F *-close -‿close 1-close , prop-1-1-2-xi-2 x∈F y∈F (-‿close 1-close) x≤y (≥-‿reverse 1-close 1≥0) ⟩
                        x * (- 1#)
                      ≈⟨ x∈F *-close -‿close 1-close , *-comm x∈F (-‿close 1-close) ⟩
                        (- 1#) * x
                      ≈⟨ -‿close 1-close *-close x∈F , negativeUnit x∈F ⟩
                        - x
                      ∎⟨ -‿close x∈F ⟩

  <-‿comp : {x y : A} → F x → F y → x < y → - y < - x
  <-‿comp {x} {y} x∈F y∈F (x≤y , x≉y)
    = ( ≤-‿comp x∈F y∈F x≤y
      , λ -y≈-x → x≉y (
        begin
            x
          ≈˘⟨ x∈F , -‿doubleInverse x∈F ⟩
            - (- x)
          ≈˘⟨ -‿close (-‿close x∈F) , -‿cong (-‿close y∈F) (-‿close x∈F) -y≈-x ⟩
            - (- y)
          ≈⟨ -‿close (-‿close y∈F) , -‿doubleInverse y∈F ⟩
            y
          ∎⟨ y∈F ⟩
        )
      )
  <-‿moveˡ : {x y : A} → F x → F y → - x < y → - y < x
  <-‿moveˡ x∈F y∈F -x<y = <≈-trans (-‿close y∈F) (-‿close (-‿close x∈F)) x∈F (<-‿comp (-‿close x∈F) y∈F -x<y) (-‿doubleInverse x∈F)

  ≤*-sign : {x y : A} → F x → F y
        → (x ≥ 0# ⊎ x ≤ 0#)
        → (y ≥ 0# ⊎ y ≤ 0#)
        → ((x * y) ≥ 0# ⊎ (x * y) ≤ 0#)
  ≤*-sign x∈F y∈F (inj₁ x≥0) (inj₁ y≥0) = inj₁ (≤*-comp x∈F y∈F x≥0 y≥0)
  ≤*-sign x∈F y∈F (inj₁ x≥0) (inj₂ y≤0) = inj₂ (prop-1-1-2-xii-3 x∈F y∈F x≥0 y≤0)
  ≤*-sign x∈F y∈F (inj₂ x≤0) (inj₁ y≥0) = inj₂ (prop-1-1-2-xii-2 x∈F y∈F x≤0 y≥0)
  ≤*-sign x∈F y∈F (inj₂ x≤0) (inj₂ y≤0) = inj₁ (prop-1-1-2-xii-1 x∈F y∈F x≤0 y≤0)

  _≤+-sign_ : {x y : A} → F x → F y
        → ((x + y) ≥ 0# ⊎ (x + y) ≤ 0#)
  x∈F ≤+-sign y∈F = sign (x∈F +-close y∈F)

  prop-1-1-5-iii : {x y : A} → (x∈F : F x) → (y∈F : F y)
                  → (x' : x ≥ 0# ⊎ x ≤ 0#)
                  → (y' : y ≥ 0# ⊎ y ≤ 0#)
                  → ∣ x * y ∣ (≤*-sign x∈F y∈F x' y') ≈ (∣ x ∣ (x')  * ∣ y ∣ (y'))
  prop-1-1-5-iii x∈F y∈F (inj₁ x≥0) (inj₁ y≥0) = ≈-refl (x∈F *-close y∈F)
  prop-1-1-5-iii {x} {y} x∈F y∈F (inj₁ x≥0) (inj₂ y≤0) = begin
                                                - (x * y)
                                                ≈⟨ -‿close (x∈F *-close y∈F) , -‿cong (x∈F *-close y∈F) (y∈F *-close x∈F) (*-comm x∈F y∈F) ⟩
                                                - (y * x)
                                                ≈˘⟨ -‿close (y∈F *-close x∈F) , -‿assoc y∈F x∈F ⟩
                                                (- y) * x
                                                ≈⟨ (-‿close y∈F) *-close x∈F , *-comm (-‿close y∈F) x∈F ⟩
                                                x * (- y)
                                                ∎⟨ x∈F *-close (-‿close y∈F) ⟩
  prop-1-1-5-iii x∈F y∈F (inj₂ x≤0) (inj₁ y≥0) = ≈-sym (-‿close x∈F *-close y∈F) (-‿close (x∈F *-close y∈F)) (-‿assoc x∈F y∈F)
  prop-1-1-5-iii x∈F y∈F (inj₂ x≤0) (inj₂ y≤0) = ≈-sym (-‿close x∈F *-close -‿close y∈F) (x∈F *-close y∈F) (*-‿cancel x∈F y∈F)
  -- postulate
  --

  lemma-triIneq-1-1 : {x y : A} → F x → F y
                    → (x' : x ≥ 0# ⊎ x ≤ 0#)
                    → x ≤ y → - x ≤ y → ∣ x ∣ x' ≤ y
  lemma-triIneq-1-1 x∈F y∈F (inj₁ x≥0) x≤y _ = x≤y
  lemma-triIneq-1-1 x∈F y∈F (inj₂ x≤0) _ = id

  lemma-triIneq-1-2 : {x y : A} → F x → F y
                    → (x' : x ≥ 0# ⊎ x ≤ 0#)
                    → ∣ x ∣ x' ≤ y
                    → (x ≤ y) × (- x ≤ y)
  lemma-triIneq-1-2 x∈F y∈F (inj₁ x≥0) x≤y = (x≤y , ≤-trans -x∈F 0-close y∈F -x≤0 0≤y)
    where -x∈F = -‿close x∈F
          -x≤0 = ≥-‿reverse x∈F x≥0
          0≤y = ≤-trans 0-close x∈F y∈F x≥0 x≤y
  lemma-triIneq-1-2 x∈F y∈F (inj₂ x≤0) -x≤y = (≤-trans x∈F 0-close y∈F x≤0 0≤y , -x≤y)
    where -x∈F = -‿close x∈F
          0≤y = ≤-trans 0-close -x∈F y∈F (≤-‿reverse x∈F x≤0) -x≤y

  lemma-triIneq-1-2' : {x y : A} → F x → F y
                    → (x' : x ≥ 0# ⊎ x ≤ 0#)
                    → ∣ x ∣ x' < y
                    → (x < y) × (- x < y)
  lemma-triIneq-1-2' x∈F y∈F (inj₁ x≥0) (x≤y , x≉y)
    = ( (proj₁ (lemma-triIneq-1-2 x∈F y∈F (inj₁ x≥0) x≤y)
        , x≉y
        )
      , (proj₂ (lemma-triIneq-1-2 x∈F y∈F (inj₁ x≥0) x≤y)
        , λ -x≈y → x≉y (-x≈y→x≈y -x≈y)
        ) -- (y ≈ -x ≤ 0 ≤ x ≤ y) → (y ≈ x) → ⊥
      ) where -x≈y→y≤0 = λ -x≈y → ≈≤-trans y∈F (-‿close x∈F) 0-close (≈-sym (-‿close x∈F) y∈F -x≈y) (≥-‿reverse x∈F x≥0)
              -x≈y→x≥y = λ -x≈y → ≤-trans y∈F 0-close x∈F (-x≈y→y≤0 -x≈y) x≥0
              -x≈y→x≈y = λ -x≈y → ≤-anti-sym x∈F y∈F x≤y (-x≈y→x≥y -x≈y)

  lemma-triIneq-1-2' x∈F y∈F (inj₂ x≤0) (-x≤y , -x≉y)
    = ( (proj₁ (lemma-triIneq-1-2 x∈F y∈F (inj₂ x≤0) -x≤y)
        , λ x≈y → -x≉y (x≈y→-x≈y x≈y)
        )
      , (proj₂ (lemma-triIneq-1-2 x∈F y∈F (inj₂ x≤0) -x≤y)
        , -x≉y
        ) -- (y ≈ x ≤ 0 ≤ -x ≤ y) → (y ≈ -x) → ⊥
      ) where x≈y→y≤0 = λ x≈y → ≈≤-trans y∈F x∈F 0-close (≈-sym x∈F y∈F x≈y) x≤0
              x≈y→-x≥y = λ x≈y → ≤-trans y∈F 0-close (-‿close x∈F) (x≈y→y≤0 x≈y) (≤-‿reverse x∈F x≤0)
              x≈y→-x≈y = λ x≈y → ≤-anti-sym (-‿close x∈F) y∈F -x≤y (x≈y→-x≥y x≈y)


  lemma-triIneq-2-1 : {x y : A} → F x → F y
                    → (x' : x ≥ 0# ⊎ x ≤ 0#)
                    → x ≤ y → - y ≤ x → ∣ x ∣ x' ≤ y
  lemma-triIneq-2-1 x∈F y∈F (inj₁ x≥0) x≤y _ = x≤y
  lemma-triIneq-2-1 {x} {y} x∈F y∈F (inj₂ x≤0) _ -y≤x
    = ≤-begin
      - x
    ≤≈⟨ -‿close x∈F , ≤-‿comp (-‿close y∈F) x∈F -y≤x ⟩
      - (- y)
    ≈⟨ -‿close (-‿close y∈F) , -‿doubleInverse y∈F ⟩
      y
    ∎⟨ y∈F ⟩

  lemma-triIneq-2-1' : {x y : A} → F x → F y
                    → (x' : x ≥ 0# ⊎ x ≤ 0#)
                    → x < y → - y < x → ∣ x ∣ x' < y
  lemma-triIneq-2-1' x∈F y∈F (inj₁ x≥0) x<y _ = x<y
  lemma-triIneq-2-1' {x} {y} x∈F y∈F (inj₂ x≤0) (x≤y , x≉y) (-y≤x , -y≉x)
    = (-x≤y , -x≉y)
    where -x≤y = lemma-triIneq-2-1 x∈F y∈F (inj₂ x≤0) x≤y -y≤x
          -x≉y = λ -x≈y → -y≉x (begin
                                  - y
                                ≈˘⟨ -‿close y∈F , -‿cong (-‿close x∈F) y∈F -x≈y ⟩
                                  - (- x)
                                ≈⟨ -‿close (-‿close x∈F) , -‿doubleInverse x∈F ⟩
                                  x
                                ∎⟨ x∈F ⟩
                                )

  lemma-triIneq-3 : {x : A} → F x
                    → (x' : x ≥ 0# ⊎ x ≤ 0#)
                    → x ≤ ∣ x ∣ x'
  lemma-triIneq-3 x∈F (inj₁ x≥0) = ≤-refl x∈F
  lemma-triIneq-3 {x} x∈F (inj₂ x≤0) = ≤-begin
                                        x
                                      ≤⟨ x∈F , x≤0 ⟩
                                        0#
                                      ≤⟨ 0-close , ≤-‿reverse x∈F x≤0 ⟩
                                        - x
                                      ≤-∎⟨ -‿close x∈F ⟩
  lemma-triIneq-4 : {x : A} → F x → (x' : x ≥ 0# ⊎ x ≤ 0#) → - x ≤ ∣ x ∣ x'
  lemma-triIneq-4 {x} x∈F (inj₁ x≥0) = ≤-begin
                                        - x
                                      ≤⟨ -‿close x∈F , ≥-‿reverse x∈F x≥0 ⟩
                                        0#
                                      ≤⟨ 0-close , x≥0 ⟩
                                        x
                                      ≤-∎⟨ x∈F ⟩
  lemma-triIneq-4 x∈F (inj₂ x≤0) = ≤-refl (-‿close x∈F)

  ∣∣-triangleIneq : {x y : A} → (x∈F : F x) → (y∈F : F y)
                  → (x' : x ≥ 0# ⊎ x ≤ 0#)
                  → (y' : y ≥ 0# ⊎ y ≤ 0#)
                  → ∣ x + y ∣ (x∈F ≤+-sign y∈F) ≤ (∣ x ∣ x' + ∣ y ∣ y')
  ∣∣-triangleIneq {x} {y} x∈F y∈F x' y'
    = lemma-triIneq-1-1 (x∈F +-close y∈F) ((∣ x∈F ∣-close  x') +-close (∣ y∈F ∣-close  y')) (x∈F ≤+-sign y∈F) x+y≤∣x∣+∣y∣ -x-y≤∣x∣+∣y∣
      where x+y≤∣x∣+∣y∣ = ≤-begin
                          x + y
                        ≤⟨ x∈F +-close y∈F , ≤+-compˡ x∈F (∣ x∈F ∣-close  x') y∈F (lemma-triIneq-3 x∈F x') ⟩
                          (∣ x ∣ x' + y)
                        ≤⟨ (∣ x∈F ∣-close  x') +-close y∈F , ≤+-compʳ y∈F (∣ y∈F ∣-close  y') (∣ x∈F ∣-close  x') (lemma-triIneq-3 y∈F y') ⟩
                          (∣ x ∣ x' + ∣ y ∣ y')
                        ≤-∎⟨ (∣ x∈F ∣-close  x') +-close (∣ y∈F ∣-close  y') ⟩
            -x-y≤∣x∣+∣y∣ = ≤-begin
                          - (x + y)
                        ≈≤⟨ -‿close (x∈F +-close y∈F) , -‿distrib x∈F y∈F ⟩
                          (- x) + (- y)
                        ≤⟨ (-‿close x∈F) +-close (-‿close y∈F) , ≤+-compˡ (-‿close x∈F) (∣ x∈F ∣-close  x') (-‿close y∈F) (lemma-triIneq-4 x∈F x') ⟩
                          ∣ x ∣ x' + (- y)
                        ≤⟨ ∣ x∈F ∣-close  x' +-close (-‿close y∈F) , ≤+-compʳ (-‿close y∈F) (∣ y∈F ∣-close  y') (∣ x∈F ∣-close  x') (lemma-triIneq-4 y∈F y') ⟩
                          ∣ x ∣ x' + ∣ y ∣ y'
                        ≤-∎⟨ (∣ x∈F ∣-close  x') +-close (∣ y∈F ∣-close  y') ⟩
  -- triangleIneq' : {x y : A} → F x → F y
  --                 → ∣ ∣ x ∣ + (- ∣ y ∣) ∣ ≤ (∣ x + (- y) ∣)

  d-sign : {x : A} → {y : A} → F x × F y
          → (x' : x ≥ 0# ⊎ x ≤ 0#)
          → (y' : y ≥ 0# ⊎ y ≤ 0#)
          → (x + (- y)) ≥ 0# ⊎ (x + (- y)) ≤ 0#
  d-sign {x} {y} (x∈F , y∈F) (inj₁ x≥0) (inj₂ y≤0) = (inj₁ (prop-1-1-2-xii-5 x∈F (-‿close y∈F) x≥0 (≤-‿reverse y∈F y≤0)))
  d-sign {x} {y} (x∈F , y∈F) (inj₂ x≤0) (inj₁ y≥0) = (inj₂ (prop-1-1-2-xii-6 x∈F (-‿close y∈F) x≤0 (≥-‿reverse y∈F y≥0)))
  d-sign {x} {y} (x∈F , y∈F) _ _ = (sign (x∈F +-close -‿close y∈F))

  d : {x y : A} → F x × F y
      → (x ≥ 0# ⊎ x ≤ 0#)
      → (y ≥ 0# ⊎ y ≤ 0#)
      → A
  d {x} {y} (x∈F , y∈F) x-sign y-sign = ∣ x + (- y) ∣ (d-sign (x∈F , y∈F) x-sign y-sign)

  d-close : {x y : A} → (x' : F x) → (y' : F y)
            → (x-sign : x ≥ 0# ⊎ x ≤ 0#)
            → (y-sign : y ≥ 0# ⊎ y ≤ 0#)
            → F (d (x' , y') x-sign y-sign)
  d-close x∈F y∈F x-sign y-sign = ∣ (x∈F +-close (-‿close y∈F)) ∣-close (d-sign (x∈F , y∈F) x-sign y-sign)

  prop-1-1-6-i : {x y : A} → (x∈F : F x) → (y∈F : F y)
                → (x-sign : x ≥ 0# ⊎ x ≤ 0#)
                → (y-sign : y ≥ 0# ⊎ y ≤ 0#)
                → 0# ≤ d (x∈F , y∈F) x-sign y-sign
  prop-1-1-6-i x∈F y∈F x-sign y-sign = prop-1-1-5-i (x∈F +-close -‿close y∈F) (d-sign (x∈F , y∈F) x-sign y-sign)

  postulate
    prop-1-1-6-ii-1 : {x y : A} → (x∈F : F x) → (y∈F : F y)
                  → (x-sign : x ≥ 0# ⊎ x ≤ 0#)
                  → (y-sign : y ≥ 0# ⊎ y ≤ 0#)
                  → (d (x∈F , y∈F) x-sign y-sign ≈ 0#)
                  → (x ≈ y)
    prop-1-1-6-ii-2 : {x y : A} → (x∈F : F x) → (y∈F : F y)
                  → (x-sign : x ≥ 0# ⊎ x ≤ 0#)
                  → (y-sign : y ≥ 0# ⊎ y ≤ 0#)
                  → (x ≈ y)
                  → (d (x∈F , y∈F) x-sign y-sign ≈ 0#)


  prop-1-1-6-ii : {x y : A} → (x∈F : F x) → (y∈F : F y)
                  → (x-sign : x ≥ 0# ⊎ x ≤ 0#)
                  → (y-sign : y ≥ 0# ⊎ y ≤ 0#)
                  → (d (x∈F , y∈F) x-sign y-sign ≈ 0#) ↔ (x ≈ y)
  prop-1-1-6-ii x∈F y∈F x-sign y-sign
    = (prop-1-1-6-ii-1 x∈F y∈F x-sign y-sign , prop-1-1-6-ii-2 x∈F y∈F x-sign y-sign)

  -- prop-1-1-6-iii : {x y : A} → (x∈F : F x) → (y∈F : F y)
  --                 → (x-sign : x ≥ 0# ⊎ x ≤ 0#)
  --                 → (y-sign : y ≥ 0# ⊎ y ≤ 0#)
  --                 → d (x∈F , y∈F) x-sign y-sign ≈ d (y∈F , x∈F) y-sign x-sign
  -- prop-1-1-6-iii {x} {y} x∈F y∈F x-sign y-sign
  --   = [ (λ x-y≥0 → begin
  --               x + (- y)
  --             ≈⟨ x∈F +-close (-‿close y∈F) , +-comm x∈F (-‿close y∈F) ⟩
  --               (- y) + x
  --             ≈˘⟨ (-‿close y∈F) +-close x∈F , +-congʳ (-‿close (-‿close x∈F)) x∈F (-‿close y∈F) (-‿doubleInverse x∈F) ⟩
  --               (- y) + (- (- x))
  --             ≈˘⟨ (-‿close y∈F) +-close (-‿close (-‿close x∈F)) , -‿distrib y∈F (-‿close x∈F) ⟩
  --               - (y + (- x))
  --             ∎⟨ -‿close (y∈F +-close (-‿close x∈F)) ⟩)
  --     , (λ x-y≤0 → begin
  --               - (x + (- y))
  --             ≈⟨ -‿close (x∈F +-close (-‿close y∈F)) , -‿distrib x∈F (-‿close y∈F) ⟩
  --               (- x) + (- (- y))
  --             ≈⟨ (-‿close x∈F) +-close (-‿close (-‿close y∈F)) , +-congʳ (-‿close (-‿close y∈F)) y∈F (-‿close x∈F) (-‿doubleInverse y∈F) ⟩
  --               (- x) + y
  --             ≈⟨ (-‿close x∈F) +-close y∈F , +-comm (-‿close x∈F) y∈F ⟩
  --               y + (- x)
  --             ∎⟨ y∈F +-close (-‿close x∈F) ⟩)
  --     ] (d-sign (x∈F , y∈F) x-sign y-sign)

  lemma-d-triIneq : {x y z : A} → F x → F y → F z
                    → (x + y) ≈ ((x + (- z)) + (z + y))
  lemma-d-triIneq {x} {y} {z} x∈F y∈F z∈F
    = begin
      x + y
    ≈˘⟨ x∈F +-close y∈F , +-congʳ (0-close +-close y∈F) y∈F x∈F (0-identityˡ y∈F) ⟩
      x + (0# + y)
    ≈˘⟨ x∈F +-close (0-close +-close y∈F) , +-congʳ (((-‿close z∈F) +-close z∈F) +-close y∈F) (0-close +-close y∈F) x∈F (+-congˡ ((-‿close z∈F) +-close z∈F) 0-close y∈F (-‿inverseˡ z∈F)) ⟩
      x + (((- z) + z) + y)
    ≈⟨ x∈F +-close (((-‿close z∈F) +-close z∈F) +-close y∈F) , +-congʳ (((-‿close z∈F) +-close z∈F) +-close y∈F) ((-‿close z∈F) +-close (z∈F +-close y∈F)) x∈F (+-assoc (-‿close z∈F) z∈F y∈F) ⟩
      x + ((- z) + (z + y))
    ≈˘⟨ x∈F +-close ((-‿close z∈F) +-close (z∈F +-close y∈F)) , +-assoc x∈F (-‿close z∈F) (z∈F +-close y∈F) ⟩
      (x + (- z)) + (z + y)
    ∎⟨ (x∈F +-close (-‿close z∈F)) +-close (z∈F +-close y∈F) ⟩

  d-triangleIneq : {x y z : A}
                  → (x∈F : F x) → (y∈F : F y)→ (z∈F : F z)
                  → (x-sign : x ≥ 0# ⊎ x ≤ 0#)
                  → (y-sign : y ≥ 0# ⊎ y ≤ 0#)
                  → (z-sign : z ≥ 0# ⊎ z ≤ 0#)
                  → d (x∈F , y∈F) x-sign y-sign
                    ≤ (d (x∈F , z∈F) x-sign z-sign
                      + d (z∈F , y∈F) z-sign y-sign)
  d-triangleIneq {x} {y} {z} x∈F y∈F z∈F x-sign y-sign z-sign
    = ≤-begin
      d (x∈F , y∈F) x-sign y-sign
    ≈≤⟨ d-close x∈F y∈F x-sign y-sign , ∣∣-cong (x∈F +-close (-‿close y∈F)) ((x∈F +-close (-‿close z∈F)) +-close (z∈F +-close (-‿close y∈F))) (d-sign (x∈F , y∈F) x-sign y-sign) ((x∈F +-close (-‿close z∈F)) ≤+-sign (z∈F +-close (-‿close y∈F))) x-y≈x-z+z-y ⟩
      ∣ (x + (- z)) + (z + (- y)) ∣ ((x∈F +-close (-‿close z∈F)) ≤+-sign (z∈F +-close (-‿close y∈F)))
    ≤⟨ ∣ ((x∈F +-close (-‿close z∈F)) +-close (z∈F +-close (-‿close y∈F))) ∣-close ((x∈F +-close (-‿close z∈F)) ≤+-sign (z∈F +-close (-‿close y∈F))) , ∣∣-triangleIneq (x∈F +-close (-‿close z∈F)) (z∈F +-close (-‿close y∈F)) (d-sign (x∈F , z∈F) x-sign z-sign) (d-sign (z∈F , y∈F) z-sign y-sign) ⟩
      (d (x∈F , z∈F) x-sign z-sign
      + d (z∈F , y∈F) z-sign y-sign)
    ≤-∎⟨ d-close x∈F z∈F x-sign z-sign +-close d-close z∈F y∈F z-sign y-sign ⟩
    where x-y≈x-z+z-y = (lemma-d-triIneq x∈F (-‿close y∈F) z∈F)
  lim_≈_ : {x : ℕ → A} → (x' : (n : ℕ) → F (x n))
          → {a : A} → F a → Set
  lim x' ≈ a' = {ε : A} → F ε → ε ≥ 0#
                  → Σ[ N ∈ ℕ ] (
                      {n : ℕ} → n ≥ᴺ N
                      → (d (x' n , a') (sign (x' n)) (sign a'))
                        < ε
                    )

  _Convergent : {x : ℕ → A} (x' : (n : ℕ) → F (x n)) → Set
  x' Convergent = Σ[ a ∈ A ] (Σ[ a' ∈ F a ] (lim x' ≈ a'))

  _Bounded : {B : Set} (x : B → A) → Set
  _Bounded {B} x = Σ[ b ∈ A ] (
                    Σ[ b' ∈ F b ] (
                      (n : B) → (x n) ≤ b
                    )
                  )

  _Increasing : (x : ℕ → A) → Set
  x Increasing = (n m : ℕ) → (n ≤ᴺ m) → (x n ≤ x m)

  _Cauchy : {x : ℕ → A} → (x' : (n : ℕ) → F (x n)) → Set
  x' Cauchy = (ε : A) → F ε → ε ≥ 0#
            → Σ[ N ∈ ℕ ] (
                (m n : ℕ) → m ≥ᴺ N → n ≥ᴺ N
                → (d (x' m , x' n) (sign (x' m)) (sign (x' n))) < ε
              )

  _+ᶠᵘⁿᶜ_ : {B : Set} (x y : B → A) → B → A
  (x +ᶠᵘⁿᶜ y) n = x n + y n
  --
  -- postulate
  sandwich-lemma : {x y z : ℕ → A}
                  → {x' : (n : ℕ) → F (x n)}
                  → {y' : (n : ℕ) → F (y n)}
                  → {z' : (n : ℕ) → F (z n)}
                  → {a : A} → {a' : F a}
                  → lim x' ≈ a' → lim y' ≈ a'
                  → (Σ[ Nx₀ ∈ ℕ ] ({n : ℕ} → n ≥ᴺ Nx₀ → (x n ≤ z n)))
                  → (Σ[ Ny₀ ∈ ℕ ] ({n : ℕ} → n ≥ᴺ Ny₀ → (z n ≤ y n)))
                  → lim z' ≈ a'
  sandwich-lemma {x} {y} {z} {x'} {y'} {z'} {a} {a'}
    limx≈a limy≈a (Nx₀ , xn≤zn) (Ny₀ , zn≤yn) {ε} ε∈F ε≥0
      = (N , n≥N→∣zn-a∣<ε)
        where Nx₁ = proj₁ (limx≈a ε∈F ε≥0)
              Ny₁ = proj₁ (limy≈a ε∈F ε≥0)
              N = maxᴺ Nx₀ (Ny₀ ∷ Nx₁ ∷ Ny₁ ∷ [])
              N≥Nx₀∷Ny₀∷Nx₁∷Ny₁ = max-order Nx₀ (Ny₀ ∷ Nx₁ ∷ Ny₁ ∷ [])
              N≥Nx₀ = proj₁ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁
              N≥Ny₀ = proj₁ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁)
              N≥Nx₁ = proj₁ (proj₂ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁))
              N≥Ny₁ = proj₁ (proj₂ (proj₂ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁)))
              n≥N→n≥Nx₀ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Nx₀} {N} {n} N≥Nx₀ n≥N)
              n≥N→n≥Ny₀ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Ny₀} {N} {n} N≥Ny₀ n≥N)
              n≥N→n≥Nx₁ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Nx₁} {N} {n} N≥Nx₁ n≥N)
              n≥N→n≥Ny₁ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Ny₁} {N} {n} N≥Ny₁ n≥N)
              n≥N→zn-a≤yn-a = λ {n} → λ n≥N → ≤+-compˡ (z' n) (y' n) (-‿close a') (zn≤yn {n} (n≥N→n≥Ny₀ n≥N))
              n≥N→∣yn-a∣<ε = proj₂ (limy≈a ε∈F ε≥0)
              n≥N→yn-a<ε = λ {n} → λ n≥N → proj₁ (lemma-triIneq-1-2' (y' n +-close (-‿close a')) ε∈F (d-sign (y' n , a') (sign (y' n)) (sign a')) (n≥N→∣yn-a∣<ε (n≥N→n≥Ny₁ n≥N)))
              n≥N→zn-a<ε = λ {n} → λ n≥N → ≤<-trans (z' n +-close (-‿close a')) (y' n +-close (-‿close a')) ε∈F (n≥N→zn-a≤yn-a n≥N) (n≥N→yn-a<ε n≥N)
              n≥N→xn-a≤zn-a = λ {n} → λ n≥N → ≤+-compˡ (x' n) (z' n) (-‿close a') (xn≤zn {n} (n≥N→n≥Nx₀ n≥N))
              n≥N→∣xn-a∣<ε = proj₂ (limx≈a ε∈F ε≥0)
              n≥N→-xn+a<ε = λ {n} → λ n≥N → proj₂ (lemma-triIneq-1-2' (x' n +-close (-‿close a')) ε∈F (d-sign (x' n , a') (sign (x' n)) (sign a')) (n≥N→∣xn-a∣<ε (n≥N→n≥Nx₁ n≥N)))
              n≥N→-ε<xn-a = λ {n : ℕ} → λ n≥N → <-‿moveˡ (x' n +-close (-‿close a')) ε∈F (n≥N→-xn+a<ε n≥N)
              n≥N→-ε<zn-a = λ {n} → λ n≥N → <≤-trans (-‿close ε∈F) (x' n +-close (-‿close a')) (z' n +-close (-‿close a')) (n≥N→-ε<xn-a n≥N) (n≥N→xn-a≤zn-a n≥N)
              n≥N→∣zn-a∣<ε = λ {n} → λ n≥N → lemma-triIneq-2-1' (z' n +-close (-‿close a')) ε∈F (d-sign ((z' n , a')) (sign (z' n)) (sign a')) (n≥N→zn-a<ε n≥N) (n≥N→-ε<zn-a n≥N)

  -- -ε < xn - a ≤ zn - a ≤ yn - a < ε
  -- lemma-triIneq-2-1
  --   prop-1-2-3 : {x : ℕ → A} → {a lb ub : A}
  --               → lim x ≈ a
  --               → ((n : ℕ) → lb ≤ a × a ≤ ub)
  --               → lb ≤ a × a ≤ ub
  --   prop-1-2-5 : {x : ℕ → A} → {a b : A}
  --               → lim x ≈ a → lim x ≈ b
  --               → a ≈ b
  --   prop-1-2-6 : {x : ℕ → A} → x Convergent → x Bounded
  --   limit-theroem-1 : {x y : ℕ → A} → {a b : A}
  --                     → lim x ≈ a → lim y ≈ b
  --                     → lim (λ n → x n + y n) ≈ (a + b)
  --   limit-theroem-2 : {x : ℕ → A} → {a c : A}
  --                     → lim x ≈ a
  --                     → lim (λ n → c * x n) ≈ (c * a)
  --   limit-theroem-3 : {x y : ℕ → A} → {a b : A}
  --                     → lim x ≈ a → lim y ≈ b
  --                     → lim (λ n → x n * y n) ≈ (a * b)
  --   limit-theroem-4 : {x y : ℕ → A} → {a b : A}
  --                     → ((n : ℕ) → ¬ (y n ≈ 0#)) → ¬ (b ≈ 0#)
  --                     → lim x ≈ a → lim y ≈ b
  --                     → lim (λ n → x n / y n) ≈ (a / b)
  --
  MonotoneSequeceProperty : Set
  MonotoneSequeceProperty = {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
                            → x Increasing → x Bounded
                            → x' Convergent
  CauchyComplete : Set
  CauchyComplete = {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
                  → x' Cauchy → x' Convergent
