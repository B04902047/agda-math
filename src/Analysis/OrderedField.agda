
module Analysis.OrderedField {A : Set} (_≈_ : A → A → Set) where

open import Analysis.OrderedSet _≈_
open import Algebra.Field _≈_
open import Basic.Logic
open import Basic.Properties _≈_
open import Basic.Subtype

open import Number.Natural
  renaming
  ( _≤_ to _≤ᴺ_
  ; _≥_ to _≥ᴺ_
  ; _<_ to _<ᴺ_
  ; _>_ to _>ᴺ_
  ; ≤-trans to ≤ᴺ-trans
  )

open import Data.List hiding ([_])


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
  open IsField isField
    hiding
      ( _IsEquivalentTo_
      ; _∎⟨_⟩
      ; _≈⟨_,_⟩_
      ; _≈˘⟨_,_⟩_
      ; _≡⟨_⟩_
      ; _≡˘⟨_⟩_
      ; _≡⟨⟩_
      ; begin_)
    public
  open IsOrderedSet isOrderedSet public

  -----------------------------------------------------------------------------
  -- ArchimedeanProperty

  data ℕ' : A → Set where
    1∈ℕ   : ℕ' 1#
    1+n∈ℕ : {n : A} → ℕ' n → ℕ' (n + 1#)
  data ℤ' : A → Set where
    0∈ℤ : ℤ' 0#
    n∈ℤ : {n : A} → ℕ' n → ℤ' n
    -n∈ℤ : {n : A} → ℤ' n → ℤ' (- n)

  ArchimedeanProperty : Set
  ArchimedeanProperty = {x : A} → F x → Σ[ n ∈ A ] (ℕ' n) × x < n

  ArchimedeanProperty' : Set
  ArchimedeanProperty' = {x y : A} → F x → F y → 0# < x → x < y
                       → Σ[ k ∈ A ] (ℕ' k) × y < (k * x)

  ArchimedeanProperty'' : Set
  ArchimedeanProperty'' = {x : A} → F x → 0# < x
                        → Σ[ n ∈ A ] (ℕ' n) × x < n

  private
    _+'_ : Closed₂ F _+_
    _+'_ = _+-close_
    _*'_ : Closed₂ F _*_
    _*'_ = _*-close_
    0' : F 0#
    0' = 0∈F
    1' : F 1#
    1' = 1∈F
    -' : Closed₁ F -
    -' = -‿close

  -----------------------------------------------------------------------------
  -- Basic comparing laws

  ≤+-compʳ : {x y z : A} → F x → F y → F z
            → x ≤ y → (z + x) ≤ (z + y)
  ≤+-compʳ {x} {y} {z} x' y' z' x≤y
    = ≤-begin
      z + x
    ≈≤⟨ z' +' x' , z' +-comm x' ⟩
      x + z
    ≤≈⟨ x' +' z' , ≤+-compˡ x' y' z' x≤y ⟩
      y + z
    ≈⟨ y' +' z' , y' +-comm z' ⟩
      z + y
    ∎⟨ z' +' y' ⟩

  ≤-‿reverse : {x : A} → F x → x ≤ 0# → (- x) ≥ 0#
  ≤-‿reverse {x} x' x≤0
    = ≤-begin
      0#
    ≈≤˘⟨ 0' , -‿inverseʳ x' ⟩
      x + (- x)
    ≤≈⟨ x' +' -' x' , ≤+-compˡ x' 0' (-' x') x≤0 ⟩
      0# + (- x)
    ≈⟨ 0' +' -' x' , 0-identityˡ (-' x') ⟩
      - x
    ∎⟨ -' x' ⟩
  ≥-‿reverse : {x : A} → F x → x ≥ 0# → (- x) ≤ 0#
  ≥-‿reverse {x} x' 0≤x
    = ≤-begin
      - x
    ≈≤˘⟨ -' x' , 0-identityˡ (-' x') ⟩
      0# + (- x)
    ≤≈⟨ 0' +' -' x' , ≤+-compˡ 0' x' (-' x') 0≤x ⟩
      x + (- x)
    ≈⟨ x' +' -' x' , -‿inverseʳ x' ⟩
      0#
    ∎⟨ 0' ⟩

  prop-1-1-2-xi-1 : {x y z : A} → F x → F y → F z
                  → x ≤ y → 0# ≤ z → (x * z) ≤ (y * z)
  prop-1-1-2-xi-1 {x} {y} {z} x' y' z' x≤y 0≤z
    = ≤-begin
      x * z
    ≈≤˘⟨ x' *' z' , 0-identityˡ (x' *' z') ⟩
      0# + (x * z)
    ≤≈⟨ 0' +' (x' *' z') , ≤+-compˡ 0' ((y' *' z') +' (-' (x' *' z'))) (x' *' z') 0≤yz-xz ⟩
      ((y * z) + (- (x * z))) + (x * z)
    ≈⟨ ((y' *' z') +' (-' (x' *' z'))) +' (x' *' z') , +-assoc (y' *' z') (-' (x' *' z')) (x' *' z') ⟩
      (y * z) + (- (x * z) + (x * z))
    ≈⟨ (y' *' z') +' ((-' (x' *' z')) +' (x' *' z')) , +-congʳ ((-' (x' *' z')) +' (x' *' z')) 0' (y' *' z') (-‿inverseˡ (x' *' z')) ⟩
      (y * z) + 0#
    ≈⟨ (y' *' z') +' 0' , (y' *' z') 0-identityʳ ⟩
      y * z
    ∎⟨ y' *' z' ⟩
    where 0≤y-x = ≤-begin
                    0#
                  ≈≤˘⟨ 0' , -‿inverseʳ x' ⟩
                    x + (- x)
                  ≤⟨ x' +' (-' x') , ≤+-compˡ x' y' (-' x') x≤y ⟩
                    y + (- x)
                  ≤-∎⟨ y' +' (-' x') ⟩
          0≤yz-xz = ≤-begin
                    0#
                  ≤≈⟨ 0' , ≤*-comp (y' +' (-' (x'))) z' 0≤y-x 0≤z ⟩
                    ((y + (- x)) * z)
                  ≈⟨ (y' +' (-' x')) *' z' , distribʳ z' y' (-' (x')) ⟩
                    (y * z) + ((- x) * z)
                  ≈⟨ (y' *' z') +' ((-' x') *' z') , +-congʳ ((-' (x')) *' z') (-' (x' *' z')) (y' *' z') (-‿assoc x' z') ⟩
                    (y * z) + (- (x * z))
                  ∎⟨ (y' *' z') +' (-' (x' *' z')) ⟩


  prop-1-1-2-xi-2 : {x y z : A} → F x → F y → F z
                  → x ≤ y → z ≤ 0# → (y * z) ≤ (x * z)
  prop-1-1-2-xi-2 {x} {y} {z} x' y' z' x≤y z≤0
    = ≤-begin
      y * z
    ≈≤˘⟨ y' *' z' , (y' *' z') 0-identityʳ ⟩
      (y * z) + 0#
    ≈≤˘⟨ (y' *' z') +' 0' , +-congʳ ((-' (x' *' z')) +' (x' *' z')) 0' (y' *' z') (-‿inverseˡ (x' *' z')) ⟩
      (y * z) + ((- (x * z)) + (x * z))
    ≈≤˘⟨ (y' *' z') +' ((-' (x' *' z')) +' (x' *' z') ) , +-assoc (y' *' z') (-' (x' *' z')) (x' *' z') ⟩
      ((y * z) + (- (x * z))) + (x * z)
    ≤≈⟨ ((y' *' z') +' (-' (x' *' z'))) +' (x' *' z') , ≤+-compˡ ((y' *' z') +' (-' (x' *' z'))) 0' (x' *' z') yz-xz≤0 ⟩
      0# + (x * z)
    ≈⟨ 0' +' (x' *' z') , 0-identityˡ (x' *' z') ⟩
      x * z
    ∎⟨ x' *' z' ⟩
    where -xz≤-yz = ≤-begin
                    - (x * z)
                  ≈≤⟨ -' (x' *' z') , -‿cong (x' *' z') (z' *' x') (x' *-comm z') ⟩
                    - (z * x)
                  ≈≤˘⟨ -' (z' *' x') , -‿assoc z' x' ⟩
                    (- z) * x
                  ≈≤⟨ (-' z') *' x' , (-' z') *-comm x' ⟩
                    x * (- z)
                  ≤≈⟨ x' *' (-' z') , prop-1-1-2-xi-1 x' y' (-' z') x≤y (≤-‿reverse z' z≤0) ⟩
                    y * (- z)
                  ≈⟨ y' *' (-' z') , y' *-comm (-' z') ⟩
                    (- z) * y
                  ≈⟨ (-' z') *' y' , -‿assoc z' y' ⟩
                    - (z * y)
                  ≈⟨ -' (z' *' y') , -‿cong (z' *' y') (y' *' z') (z' *-comm y') ⟩
                    - (y * z)
                  ∎⟨ -' (y' *' z') ⟩
          yz-xz≤0 = ≤-begin
                    (y * z) + (- (x * z))
                  ≤≈⟨ (y' *' z') +' (-' (x' *' z')) , ≤+-compʳ (-' (x' *' z')) (-' (y' *' z')) (y' *' z') -xz≤-yz ⟩
                    (y * z) + (- (y * z))
                  ≈⟨ (y' *' z') +' (-' (y' *' z')) , -‿inverseʳ (y' *' z') ⟩
                    0#
                  ∎⟨ 0' ⟩


  prop-1-1-2-xii-1 : {x y : A} → F x → F y
                  → x ≤ 0# → y ≤ 0# → 0# ≤ (x * y)
  prop-1-1-2-xii-1 {x} {y} x' y' x≤0 y≤0
    = ≤-begin
      0#
    ≤≈⟨ 0' , ≤*-comp (-' x') (-' y') (≤-‿reverse x' x≤0) (≤-‿reverse y' y≤0) ⟩
      ((- x) * (- y))
    ≈⟨ (-' x') *' (-' y') , *-‿cancel x' y' ⟩
      x * y
    ∎⟨ x' *' y' ⟩

  prop-1-1-2-xii-2 : {x y : A} → F x → F y
                  → x ≤ 0# → y ≥ 0# → (x * y) ≤ 0#
  prop-1-1-2-xii-2 {x} {y} x' y' x≤0 y≥0
    = ≤-begin
      x * y
    ≈≤˘⟨ x' *' y' , -‿doubleInverse (x' *' y') ⟩
      - (- (x * y))
    ≤≈⟨ -' (-' (x' *' y')) , ≥-‿reverse (-' (x' *' y')) -xy≥0 ⟩
      0#
    ∎⟨ 0' ⟩
    where -xy≥0 = ≤-begin
                  0#
                ≤≈⟨ 0' , prop-1-1-2-xii-1 x' (-' y') x≤0 (≥-‿reverse y' y≥0) ⟩
                  x * (- y)
                ≈⟨ x' *' (-' y') , x' *-comm (-' y') ⟩
                  (- y) * x
                ≈⟨ (-' y') *' x' , -‿assoc y' x' ⟩
                  - (y * x)
                ≈⟨ -' (y' *' x') , -‿cong (y' *' x') (x' *' y') (y' *-comm x') ⟩
                  - (x * y)
                ∎⟨ -' (x' *' y') ⟩
  prop-1-1-2-xii-3 : {x y : A} → F x → F y
                  → x ≥ 0# → y ≤ 0# → (x * y) ≤ 0#
  prop-1-1-2-xii-3 {x} {y} x' y' x≥0 y≤0
    = ≤-begin
      x * y
    ≈≤⟨ x' *' y' , x' *-comm y' ⟩
      y * x
    ≤≈⟨ y' *' x' , (prop-1-1-2-xii-2 y' x' y≤0 x≥0) ⟩
      0#
    ∎⟨ 0' ⟩
  prop-1-1-2-xii-4 : {x y : A} → F x → F y
                      → x ≥ 0# → y ≥ 0# → (x * y) ≥ 0#
  prop-1-1-2-xii-4 {x} {y} x' y' x≥0 y≥0
      = ≤-begin
        0#
      ≈≤˘⟨ 0' , 0-zeroˡ y' ⟩
        0# * y
      ≤⟨ 0' *' y' , prop-1-1-2-xi-1 0' x' y' x≥0 y≥0 ⟩
        x * y
      ≤-∎⟨ x' *' y' ⟩
  prop-1-1-2-xii-5 : {x y : A} → F x → F y
                      → x ≥ 0# → y ≥ 0# → (x + y) ≥ 0#
  prop-1-1-2-xii-5 {x} {y} x' y' x≥0 y≥0
      = ≤-begin
        0#
      ≈≤˘⟨ 0' , 0' 0-identityʳ ⟩
        0# + 0#
      ≤⟨ 0' +' 0' , ≤+-compˡ 0' x' 0' x≥0 ⟩
        x + 0#
      ≤⟨ x' +' 0' , ≤+-compʳ 0' y' x' y≥0 ⟩
        x + y
      ≤-∎⟨ x' +' y' ⟩
  prop-1-1-2-xii-6 : {x y : A} → F x → F y
                      → x ≤ 0# → y ≤ 0# → (x + y) ≤ 0#
  prop-1-1-2-xii-6 {x} {y} x' y' x≤0 y≤0
      = ≤-begin
        x + y
      ≤⟨ x' +' y' , ≤+-compʳ y'  0' x' y≤0 ⟩
        x + 0#
      ≤≈⟨ x' +' 0' , ≤+-compˡ x' 0'  0' x≤0 ⟩
        0# + 0#
      ≈⟨ 0' +' 0' , 0' 0-identityʳ ⟩
        0#
      ∎⟨ 0' ⟩


  sign : {x : A} → F x → (x ≥ 0# ⊎ x ≤ 0#)
  sign = ≤-connex 0'

  prop-1-1-2-xiv : {x : A} → F x → 0# ≤ (x * x)
  prop-1-1-2-xiv {x} x' = [ (λ 0≤x → ≤*-comp x' x' 0≤x 0≤x) , (λ x≤0 → prop-1-1-2-xii-1 x' x' x≤0 x≤0) ] (sign x')

  -----------------------------------------------------------------------------
  -- absolute value

  ∣_∣ : {x : A} → F x → A
  -- abs {x} x' = [ (λ _ → x) , (λ _ → - x)] (≤-connex 0' x')
  ∣_∣ {x} x' with (≤-connex 0' x')
  ∣_∣ {x} x' | (inj₁ x≥0) = x
  ∣_∣ {x} x' | (inj₂ x≤0) = - x

  ∣_∣-close : {x : A} → (x' : F x) → F ∣ x' ∣
  ∣ x' ∣-close with (≤-connex 0' x')
  ∣ x' ∣-close | (inj₁ x≥0) = x'
  ∣ x' ∣-close | (inj₂ x≤0) = -' x'

  -- ∣_∣ : (x : A) → x ≥ 0# ⊎ x ≤ 0# → A
  -- ∣ x ∣ (inj₁ x≥0) = x
  -- ∣ x ∣ (inj₂ x≤0) = - x
  --
  -- ∣_∣-close : {x : A} → F x → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --             → F (∣ x ∣ x')
  -- ∣ x' ∣-close (inj₁ x≥0) = x'
  -- ∣ x' ∣-close (inj₂ x≤0) = -' x'

  private
    ∣_∣' : {x : A} → (x' : F x) → F ∣ x' ∣
    ∣_∣' = ∣_∣-close

  prop-1-1-5-i' : {x : A} → (x' : F x) → 0# ≤ ∣ x' ∣
  -- prop-1-1-5-i' {x} x' = [(λ x≥0 → x≥0) , (λ x≤0 → ≤-‿reverse x' x≤0)] (≤-connex 0' x')
  prop-1-1-5-i' {x} x' with (sign x')
  prop-1-1-5-i' {x} x' | (inj₁ x≥0) = x≥0
  prop-1-1-5-i' {x} x' | (inj₂ x≤0) = ≤-‿reverse x' x≤0

  --- alternative definition

  lemma-1-1-5-ii-1 : {x : A} → F x → (x ≈ 0#) → (- x ≈ 0#)
  lemma-1-1-5-ii-1 {x} x' x≈0
    = begin
      - x
    ≈˘⟨ -' x' , 0-identityˡ (-' x') ⟩
      0# + (- x)
    ≈˘⟨ 0' +' -' x' , +-congˡ x' 0' (-' x') x≈0 ⟩
      x + (- x)
    ≈⟨ x' +' -' x' , -‿inverseʳ x' ⟩
      0#
    ∎⟨ 0' ⟩

  lemma-1-1-5-ii-2 : {x : A} → F x → (- x ≈ 0#) → (x ≈ 0#)
  lemma-1-1-5-ii-2 {x} x' -x≈0
        = begin
          x
        ≈˘⟨ x' , -‿doubleInverse x' ⟩
          - (- x)
        ≈⟨ -' (-' x') , lemma-1-1-5-ii-1 (-' x') -x≈0 ⟩
          0#
        ∎⟨ 0' ⟩

  prop-1-1-5-ii : {x : A} → (x' : F x) → (∣ x' ∣ ≈ 0#) ↔ (x ≈ 0#)
  prop-1-1-5-ii x' with sign x'
  prop-1-1-5-ii x' | (inj₁ x≥0) = (id , id)
  prop-1-1-5-ii x' | (inj₂ x≤0) = (lemma-1-1-5-ii-2 x' , lemma-1-1-5-ii-1 x')

  ∣∣-cong : {x y : A} → (x' : F x) → (y' : F y)
            → x ≈ y → ∣ x' ∣ ≈ ∣ y' ∣
  ∣∣-cong {x} {y} x' y' x≈y with sign x'
  ∣∣-cong {x} {y} x' y' x≈y | (inj₁ x≥0) with sign y'
  ∣∣-cong {x} {y} x' y' x≈y | (inj₁ x≥0) | (inj₁ y≥0) = x≈y
  ∣∣-cong {x} {y} x' y' x≈y | (inj₁ x≥0) | (inj₂ y≤0)
    = begin
      x
    ≈˘⟨ x' , proj₂ y≈0∧0≈x ⟩
      0#
    ≈˘⟨ 0' , lemma-1-1-5-ii-1 y' (proj₁ y≈0∧0≈x) ⟩
      - y
    ∎⟨ -' y' ⟩
    where y≈0∧0≈x = ≤≈-sandwich y' x' 0' y≤0 x≥0 (≈-sym x' y' x≈y)
  ∣∣-cong {x} {y} x' y' x≈y | (inj₂ x≤0) with (≤-connex 0' y')
  ∣∣-cong {x} {y} x' y' x≈y | (inj₂ x≤0) | (inj₁ y≥0)
    = begin
      - x
    ≈⟨ -' x' , lemma-1-1-5-ii-1 x' (proj₁ x≈0∧0≈y) ⟩
      0#
    ≈⟨ 0' , proj₂ x≈0∧0≈y ⟩
      y
    ∎⟨ y' ⟩
    where x≈0∧0≈y = ≤≈-sandwich x' y' 0' x≤0 y≥0 x≈y
  ∣∣-cong {x} {y} x' y' x≈y | (inj₂ x≤0) | (inj₂ y≤0) = -‿cong x' y' x≈y

  lemma-1-1-2-xiii : 1# ≤ 0# → 0# ≤ 1#
  lemma-1-1-2-xiii 1≤0 = ⊥-elim false
                        where -1≥0 = ≤-‿reverse 1' 1≤0
                              1*-1≤0 = prop-1-1-2-xii-2 1' (-' 1') 1≤0 -1≥0
                              -1≤0 = ≤-begin
                                      - 1#
                                    ≈≤˘⟨ -' 1' , 1-identityˡ (-' 1') ⟩
                                      1# * (- 1#)
                                    ≤⟨ 1' *' -' 1' , 1*-1≤0 ⟩
                                      0#
                                    ≤-∎⟨ 0' ⟩
                              -1≈0 = ≤-anti-sym (-' 1') 0' -1≤0 -1≥0
                              1≈0 = lemma-1-1-5-ii-2 1' -1≈0
                              false = 1≉0 1≈0
  1≥0 : 0# ≤ 1#
  1≥0 with sign 1'
  1≥0 | (inj₁ 1≥0) = 1≥0
  1≥0 | (inj₂ 1≤0) = lemma-1-1-2-xiii 1≤0

  ≤-‿comp : {x y : A} → F x → F y → x ≤ y → - y ≤ - x
  ≤-‿comp {x} {y} x' y' x≤y = ≤-begin
                        - y
                      ≈≤˘⟨ -' y' , negativeUnit y' ⟩
                        (- 1#) * y
                      ≈≤⟨ -' 1' *' y' , (-' 1') *-comm  y' ⟩
                        y * (- 1#)
                      ≤≈⟨ y' *' -' 1' , prop-1-1-2-xi-2 x' y' (-' 1') x≤y (≥-‿reverse 1' 1≥0) ⟩
                        x * (- 1#)
                      ≈⟨ x' *' -' 1' , x' *-comm  (-' 1') ⟩
                        (- 1#) * x
                      ≈⟨ -' 1' *' x' , negativeUnit x' ⟩
                        - x
                      ∎⟨ -' x' ⟩

  <-‿comp : {x y : A} → F x → F y → x < y → - y < - x
  <-‿comp {x} {y} x' y' (x≤y , x≉y)
    = ( ≤-‿comp x' y' x≤y
      , λ -y≈-x → x≉y (
        begin
            x
          ≈˘⟨ x' , -‿doubleInverse x' ⟩
            - (- x)
          ≈˘⟨ -' (-' x') , -‿cong (-' y') (-' x') -y≈-x ⟩
            - (- y)
          ≈⟨ -' (-' y') , -‿doubleInverse y' ⟩
            y
          ∎⟨ y' ⟩
        )
      )
  <-‿moveˡ : {x y : A} → F x → F y → - x < y → - y < x
  <-‿moveˡ x' y' -x<y = <≈-trans (-' y') (-' (-' x')) x' (<-‿comp (-' x') y' -x<y) (-‿doubleInverse x')

  _*-sign_ : {x y : A} → F x → F y
        → ((x * y) ≥ 0# ⊎ (x * y) ≤ 0#)
  x' *-sign y' with sign x'
  x' *-sign y' | (inj₁ x≥0) with sign y'
  x' *-sign y' | (inj₁ x≥0) | (inj₁ y≥0) = inj₁ (≤*-comp x' y' x≥0 y≥0)
  x' *-sign y' | (inj₁ x≥0) | (inj₂ y≤0) = inj₂ (prop-1-1-2-xii-3 x' y' x≥0 y≤0)
  x' *-sign y' | (inj₂ x≤0) with sign y'
  x' *-sign y' | (inj₂ x≤0) | (inj₁ y≥0) = inj₂ (prop-1-1-2-xii-2 x' y' x≤0 y≥0)
  x' *-sign y' | (inj₂ x≤0) | (inj₂ y≤0) = inj₁ (prop-1-1-2-xii-1 x' y' x≤0 y≤0)

  _+-sign_ : {x y : A} → F x → F y
        → ((x + y) ≥ 0# ⊎ (x + y) ≤ 0#)
  _+-sign_ {x} {y} x' y' with sign x'
  _+-sign_ {x} {y} x' y' | (inj₁ x≥0) with sign y'
  _+-sign_ {x} {y} x' y' | (inj₁ x≥0) | (inj₁ y≥0)
    = inj₁ (
        ≤-begin
          0#
        ≈≤˘⟨ 0' , 0' 0-identityʳ ⟩
          0# + 0#
        ≤⟨ 0' +' 0' , ≤+-compˡ 0' x' 0' x≥0 ⟩
          x + 0#
        ≤⟨ x' +' 0' , ≤+-compʳ 0' y' x' y≥0 ⟩
          x + y
        ≤-∎⟨ x' +' y' ⟩
      )
  _+-sign_ {x} {y} x' y' | (inj₁ x≥0) | (inj₂ y≤0) = sign (x' +' y')
  _+-sign_ {x} {y} x' y' | (inj₂ x≤0) with sign y'
  _+-sign_ {x} {y} x' y' | (inj₂ x≤0) | (inj₁ y≥0) = sign (x' +' y')
  _+-sign_ {x} {y} x' y' | (inj₂ x≤0) | (inj₂ y≤0)
    = inj₂ (
        ≤-begin
          x + y
        ≤⟨ x' +' y' , ≤+-compʳ y' 0' x' y≤0 ⟩
          x + 0#
        ≤≈⟨ x' +' 0' , ≤+-compˡ x' 0' 0' x≤0 ⟩
          0# + 0#
        ≈⟨ 0' +' 0' , 0' 0-identityʳ ⟩
          0#
        ∎⟨ 0' ⟩
      )

  -- private
  --   *'' : {x y : A} → F x → F y
  --         → (x ≥ 0# ⊎ x ≤ 0#)
  --         → (y ≥ 0# ⊎ y ≤ 0#)
  --         → ((x * y) ≥ 0# ⊎ (x * y) ≤ 0#)
  --   *'' = *-sign
  --   _+''_ : {x y : A} → F x → F y
  --         → ((x + y) ≥ 0# ⊎ (x + y) ≤ 0#)
  --   _+''_ = _+-sign_
  --
  -- prop-1-1-5-iii : {x y : A} → (x' : F x) → (y' : F y)
  --                 → ∣ x' *' y' ∣ ≈ (∣ x' ∣ * ∣ y' ∣)
  -- prop-1-1-5-iii {x} {y} x' y' with sign x' | sign y'
  -- prop-1-1-5-iii {x} {y} x' y' | (inj₁ x≥0) | (inj₁ y≥0) = {!   !}
  -- prop-1-1-5-iii {x} {y} x' y' | (inj₁ x≥0) | (inj₂ y≤0) = {!   !}
  -- prop-1-1-5-iii {x} {y} x' y' | (inj₂ x≤0) | (inj₁ y≥0) = {!   !}
  -- prop-1-1-5-iii {x} {y} x' y' | (inj₂ x≤0) | (inj₂ y≤0) = {!   !}
  -- prop-1-1-5-iii x' y' (inj₁ x≥0) (inj₁ y≥0) = ≈-refl (x' *' y')
  -- prop-1-1-5-iii {x} {y} x' y' (inj₁ x≥0) (inj₂ y≤0) = begin
  --                                               - (x * y)
  --                                               ≈⟨ -' (x' *' y') , -‿cong (x' *' y') (y' *' x') (x' *-comm y') ⟩
  --                                               - (y * x)
  --                                               ≈˘⟨ -' (y' *' x') , -‿assoc y' x' ⟩
  --                                               (- y) * x
  --                                               ≈⟨ (-' y') *' x' , (-' y') *-comm x' ⟩
  --                                               x * (- y)
  --                                               ∎⟨ x' *' (-' y') ⟩
  -- prop-1-1-5-iii x' y' (inj₂ x≤0) (inj₁ y≥0) = ≈-sym (-' x' *' y') (-' (x' *' y')) (-‿assoc x' y')
  -- prop-1-1-5-iii x' y' (inj₂ x≤0) (inj₂ y≤0) = ≈-sym (-' x' *' -' y') (x' *' y') (*-‿cancel x' y')
  -- -- postulate
  -- --
  --

  -- lemma-triIneq-1-1 : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → x ≤ y → - x ≤ y → ∣ x ∣ x' ≤ y
  -- lemma-triIneq-1-1 x' y' (inj₁ x≥0) x≤y _ = x≤y
  -- lemma-triIneq-1-1 x' y' (inj₂ x≤0) _ = id
  --
  -- lemma-triIneq-1-2 : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → ∣ x ∣ x' ≤ y
  --                   → (x ≤ y) × (- x ≤ y)
  -- lemma-triIneq-1-2 x' y' (inj₁ x≥0) x≤y = (x≤y , ≤-trans -x' 0' y' -x≤0 0≤y)
  --   where -x' = -' x'
  --         -x≤0 = ≥-‿reverse x' x≥0
  --         0≤y = ≤-trans 0' x' y' x≥0 x≤y
  -- lemma-triIneq-1-2 x' y' (inj₂ x≤0) -x≤y = (≤-trans x' 0' y' x≤0 0≤y , -x≤y)
  --   where -x' = -' x'
  --         0≤y = ≤-trans 0' -x' y' (≤-‿reverse x' x≤0) -x≤y
  --
  -- lemma-triIneq-1-2' : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → ∣ x ∣ x' < y
  --                   → (x < y) × (- x < y)
  -- lemma-triIneq-1-2' x' y' (inj₁ x≥0) (x≤y , x≉y)
  --   = ( (proj₁ (lemma-triIneq-1-2 x' y' (inj₁ x≥0) x≤y)
  --       , x≉y


  -- lemma-triIneq-1-1 : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → x ≤ y → - x ≤ y → ∣ x ∣ x' ≤ y
  -- lemma-triIneq-1-1 x' y' (inj₁ x≥0) x≤y _ = x≤y
  -- lemma-triIneq-1-1 x' y' (inj₂ x≤0) _ = id
  --
  -- lemma-triIneq-1-2 : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → ∣ x ∣ x' ≤ y
  --                   → (x ≤ y) × (- x ≤ y)
  -- lemma-triIneq-1-2 x' y' (inj₁ x≥0) x≤y = (x≤y , ≤-trans -x' 0' y' -x≤0 0≤y)
  --   where -x' = -' x'
  --         -x≤0 = ≥-‿reverse x' x≥0
  --         0≤y = ≤-trans 0' x' y' x≥0 x≤y
  -- lemma-triIneq-1-2 x' y' (inj₂ x≤0) -x≤y = (≤-trans x' 0' y' x≤0 0≤y , -x≤y)
  --   where -x' = -' x'
  --         0≤y = ≤-trans 0' -x' y' (≤-‿reverse x' x≤0) -x≤y
  --
  -- lemma-triIneq-1-2' : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → ∣ x ∣ x' < y
  --                   → (x < y) × (- x < y)
  -- lemma-triIneq-1-2' x' y' (inj₁ x≥0) (x≤y , x≉y)
  --   = ( (proj₁ (lemma-triIneq-1-2 x' y' (inj₁ x≥0) x≤y)
  --       , x≉y
  --       )
  --     , (proj₂ (lemma-triIneq-1-2 x' y' (inj₁ x≥0) x≤y)
  --       , λ -x≈y → x≉y (-x≈y→x≈y -x≈y)
  --       ) -- (y ≈ -x ≤ 0 ≤ x ≤ y) → (y ≈ x) → ⊥
  --     ) where -x≈y→y≤0 = λ -x≈y → ≈≤-trans y' (-' x') 0' (≈-sym (-' x') y' -x≈y) (≥-‿reverse x' x≥0)
  --             -x≈y→x≥y = λ -x≈y → ≤-trans y' 0' x' (-x≈y→y≤0 -x≈y) x≥0
  --             -x≈y→x≈y = λ -x≈y → ≤-anti-sym x' y' x≤y (-x≈y→x≥y -x≈y)
  --
  -- lemma-triIneq-1-2' x' y' (inj₂ x≤0) (-x≤y , -x≉y)
  --   = ( (proj₁ (lemma-triIneq-1-2 x' y' (inj₂ x≤0) -x≤y)
  --       , λ x≈y → -x≉y (x≈y→-x≈y x≈y)
  --       )
  --     , (proj₂ (lemma-triIneq-1-2 x' y' (inj₂ x≤0) -x≤y)
  --       , -x≉y
  --       ) -- (y ≈ x ≤ 0 ≤ -x ≤ y) → (y ≈ -x) → ⊥
  --     ) where x≈y→y≤0 = λ x≈y → ≈≤-trans y' x' 0' (≈-sym x' y' x≈y) x≤0
  --             x≈y→-x≥y = λ x≈y → ≤-trans y' 0' (-' x') (x≈y→y≤0 x≈y) (≤-‿reverse x' x≤0)
  --             x≈y→-x≈y = λ x≈y → ≤-anti-sym (-' x') y' -x≤y (x≈y→-x≥y x≈y)
  --
  --
  -- lemma-triIneq-2-1 : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → x ≤ y → - y ≤ x → ∣ x ∣ x' ≤ y
  -- lemma-triIneq-2-1 x' y' (inj₁ x≥0) x≤y _ = x≤y
  -- lemma-triIneq-2-1 {x} {y} x' y' (inj₂ x≤0) _ -y≤x
  --   = ≤-begin
  --     - x
  --   ≤≈⟨ -' x' , ≤-‿comp (-' y') x' -y≤x ⟩
  --     - (- y)
  --   ≈⟨ -' (-' y') , -‿doubleInverse y' ⟩
  --     y
  --   ∎⟨ y' ⟩
  --
  -- lemma-triIneq-2-1' : {x y : A} → F x → F y
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → x < y → - y < x → ∣ x ∣ x' < y
  -- lemma-triIneq-2-1' x' y' (inj₁ x≥0) x<y _ = x<y
  -- lemma-triIneq-2-1' {x} {y} x' y' (inj₂ x≤0) (x≤y , x≉y) (-y≤x , -y≉x)
  --   = (-x≤y , -x≉y)
  --   where -x≤y = lemma-triIneq-2-1 x' y' (inj₂ x≤0) x≤y -y≤x
  --         -x≉y = λ -x≈y → -y≉x (begin
  --                                 - y
  --                               ≈˘⟨ -' y' , -‿cong (-' x') y' -x≈y ⟩
  --                                 - (- x)
  --                               ≈⟨ -' (-' x') , -‿doubleInverse x' ⟩
  --                                 x
  --                               ∎⟨ x' ⟩
  --                               )
  --
  -- lemma-triIneq-3 : {x : A} → F x
  --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --                   → x ≤ ∣ x ∣ x'
  -- lemma-triIneq-3 x' (inj₁ x≥0) = ≤-refl x'
  -- lemma-triIneq-3 {x} x' (inj₂ x≤0) = ≤-begin
  --                                       x
  --                                     ≤⟨ x' , x≤0 ⟩
  --                                       0#
  --                                     ≤⟨ 0' , ≤-‿reverse x' x≤0 ⟩
  --                                       - x
  --                                     ≤-∎⟨ -' x' ⟩
  -- lemma-triIneq-4 : {x : A} → F x → (x' : x ≥ 0# ⊎ x ≤ 0#) → - x ≤ ∣ x ∣ x'
  -- lemma-triIneq-4 {x} x' (inj₁ x≥0) = ≤-begin
  --                                       - x
  --                                     ≤⟨ -' x' , ≥-‿reverse x' x≥0 ⟩
  --                                       0#
  --                                     ≤⟨ 0' , x≥0 ⟩
  --                                       x
  --                                     ≤-∎⟨ x' ⟩
  -- lemma-triIneq-4 x' (inj₂ x≤0) = ≤-refl (-' x')
  --
  -- ∣∣-triangleIneq : {x y : A} → (x' : F x) → (y' : F y)
  --                 → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  --                 → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  --                 → ∣ x + y ∣ (x' +'' y') ≤ (∣ x ∣ x'' + ∣ y ∣ y'')
  -- ∣∣-triangleIneq {x} {y} x' y' x'' y''
  --   = lemma-triIneq-1-1 (x' +' y') ((∣ x' ∣'  x'') +' (∣ y' ∣'  y'')) (x' +'' y') x+y≤∣x∣+∣y∣ -x-y≤∣x∣+∣y∣
  --     where x+y≤∣x∣+∣y∣ = ≤-begin
  --                         x + y
  --                       ≤⟨ x' +' y' , ≤+-compˡ x' (∣ x' ∣'  x'') y' (lemma-triIneq-3 x' x'') ⟩
  --                         (∣ x ∣ x'' + y)
  --                       ≤⟨ (∣ x' ∣'  x'') +' y' , ≤+-compʳ y' (∣ y' ∣'  y'') (∣ x' ∣'  x'') (lemma-triIneq-3 y' y'') ⟩
  --                         (∣ x ∣ x'' + ∣ y ∣ y'')
  --                       ≤-∎⟨ (∣ x' ∣'  x'') +' (∣ y' ∣'  y'') ⟩
  --           -x-y≤∣x∣+∣y∣ = ≤-begin
  --                         - (x + y)
  --                       ≈≤⟨ -' (x' +' y') , -‿distrib x' y' ⟩
  --                         (- x) + (- y)
  --                       ≤⟨ (-' x') +' (-' y') , ≤+-compˡ (-' x') (∣ x' ∣'  x'') (-' y') (lemma-triIneq-4 x' x'') ⟩
  --                         ∣ x ∣ x'' + (- y)
  --                       ≤⟨ ∣ x' ∣'  x'' +' (-' y') , ≤+-compʳ (-' y') (∣ y' ∣'  y'') (∣ x' ∣'  x'') (lemma-triIneq-4 y' y'') ⟩
  --                         ∣ x ∣ x'' + ∣ y ∣ y''
  --                       ≤-∎⟨ (∣ x' ∣'  x'') +' (∣ y' ∣'  y'') ⟩
  -- -- triangleIneq' : {x y : A} → F x → F y
  -- --                 → ∣ ∣ x ∣ + (- ∣ y ∣) ∣ ≤ (∣ x + (- y) ∣)
  --
  --
  -- -----------------------------------------------------------------------------
  -- -- distance
  --
  -- d-sign : {x : A} → {y : A} → F x × F y
  --         → (x' : x ≥ 0# ⊎ x ≤ 0#)
  --         → (y' : y ≥ 0# ⊎ y ≤ 0#)
  --         → (x + (- y)) ≥ 0# ⊎ (x + (- y)) ≤ 0#
  -- d-sign {x} {y} (x' , y') (inj₁ x≥0) (inj₂ y≤0) = (inj₁ (prop-1-1-2-xii-5 x' (-' y') x≥0 (≤-‿reverse y' y≤0)))
  -- d-sign {x} {y} (x' , y') (inj₂ x≤0) (inj₁ y≥0) = (inj₂ (prop-1-1-2-xii-6 x' (-' y') x≤0 (≥-‿reverse y' y≥0)))
  -- d-sign {x} {y} (x' , y') _          _          = x' +-sign (-' y') -- undicided
  -- -- d'' {x} {y} (x' , y') (inj₁ x≥0) (inj₁ y≥0)
  -- --   = [ ( λ x≤y → inj₂ (
  -- --           ≤-begin
  -- --             x + (- y)
  -- --           ≤≈⟨ x' +' (-' y') , ≤+-compˡ x' y' (-' y') x≤y ⟩
  -- --             y + (- y)
  -- --           ≈⟨ y' +' (-' y') , -‿inverseʳ y' ⟩
  -- --             0#
  -- --           ∎⟨ 0' ⟩
  -- --         )
  -- --       )
  -- --     , ( λ x≥y → inj₁ (
  -- --           ≤-begin
  -- --             0#
  -- --           ≈≤˘⟨ 0' , -‿inverseʳ y' ⟩
  -- --             y + (- y)
  -- --           ≤⟨ y' +' (-' y') , ≤+-compˡ y' x' (-' y') x≥y ⟩
  -- --             x + (- y)
  -- --           ≤-∎⟨ x' +' (-' y') ⟩
  -- --         )
  -- --       )
  -- --     ] (≤-connex x' y')
  -- -- d'' {x} {y} (x' , y') (inj₂ x≤0) (inj₂ y≤0)
  -- --   = [ ( λ -x≤-y → inj₁ (
  -- --           ≤-begin
  -- --             0#
  -- --           ≈≤˘⟨ 0' , -‿inverseʳ x' ⟩
  -- --             x + (- x)
  -- --           ≤⟨ x' +' (-' x') , ≤+-compʳ (-' x') (-' y') x' -x≤-y ⟩
  -- --             x + (- y)
  -- --           ≤-∎⟨ x' +' (-' y') ⟩
  -- --         )
  --
  -- --       )
  -- --     , (proj₂ (lemma-triIneq-1-2 x' y' (inj₁ x≥0) x≤y)
  -- --       , λ -x≈y → x≉y (-x≈y→x≈y -x≈y)
  -- --       ) -- (y ≈ -x ≤ 0 ≤ x ≤ y) → (y ≈ x) → ⊥
  -- --     ) where -x≈y→y≤0 = λ -x≈y → ≈≤-trans y' (-' x') 0' (≈-sym (-' x') y' -x≈y) (≥-‿reverse x' x≥0)
  -- --             -x≈y→x≥y = λ -x≈y → ≤-trans y' 0' x' (-x≈y→y≤0 -x≈y) x≥0
  -- --             -x≈y→x≈y = λ -x≈y → ≤-anti-sym x' y' x≤y (-x≈y→x≥y -x≈y)
  -- --
  -- -- lemma-triIneq-1-2' x' y' (inj₂ x≤0) (-x≤y , -x≉y)
  -- --   = ( (proj₁ (lemma-triIneq-1-2 x' y' (inj₂ x≤0) -x≤y)
  -- --       , λ x≈y → -x≉y (x≈y→-x≈y x≈y)
  -- --       )
  -- --     , (proj₂ (lemma-triIneq-1-2 x' y' (inj₂ x≤0) -x≤y)
  -- --       , -x≉y
  -- --       ) -- (y ≈ x ≤ 0 ≤ -x ≤ y) → (y ≈ -x) → ⊥
  -- --     ) where x≈y→y≤0 = λ x≈y → ≈≤-trans y' x' 0' (≈-sym x' y' x≈y) x≤0
  -- --             x≈y→-x≥y = λ x≈y → ≤-trans y' 0' (-' x') (x≈y→y≤0 x≈y) (≤-‿reverse x' x≤0)
  -- --             x≈y→-x≈y = λ x≈y → ≤-anti-sym (-' x') y' -x≤y (x≈y→-x≥y x≈y)
  -- --
  -- --
  -- -- lemma-triIneq-2-1 : {x y : A} → F x → F y
  -- --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                   → x ≤ y → - y ≤ x → ∣ x ∣ x' ≤ y
  -- -- lemma-triIneq-2-1 x' y' (inj₁ x≥0) x≤y _ = x≤y
  -- -- lemma-triIneq-2-1 {x} {y} x' y' (inj₂ x≤0) _ -y≤x
  -- --   = ≤-begin
  -- --     - x
  -- --   ≤≈⟨ -' x' , ≤-‿comp (-' y') x' -y≤x ⟩
  -- --     - (- y)
  -- --   ≈⟨ -' (-' y') , -‿doubleInverse y' ⟩
  -- --     y
  -- --   ∎⟨ y' ⟩
  -- --
  -- -- lemma-triIneq-2-1' : {x y : A} → F x → F y
  -- --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                   → x < y → - y < x → ∣ x ∣ x' < y
  -- -- lemma-triIneq-2-1' x' y' (inj₁ x≥0) x<y _ = x<y
  -- -- lemma-triIneq-2-1' {x} {y} x' y' (inj₂ x≤0) (x≤y , x≉y) (-y≤x , -y≉x)
  -- --   = (-x≤y , -x≉y)
  -- --   where -x≤y = lemma-triIneq-2-1 x' y' (inj₂ x≤0) x≤y -y≤x
  -- --         -x≉y = λ -x≈y → -y≉x (begin
  -- --                                 - y
  -- --                               ≈˘⟨ -' y' , -‿cong (-' x') y' -x≈y ⟩
  -- --                                 - (- x)
  -- --                               ≈⟨ -' (-' x') , -‿doubleInverse x' ⟩
  -- --                                 x
  -- --                               ∎⟨ x' ⟩
  -- --                               )
  -- --
  -- -- lemma-triIneq-3 : {x : A} → F x
  -- --                   → (x' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                   → x ≤ ∣ x ∣ x'
  -- -- lemma-triIneq-3 x' (inj₁ x≥0) = ≤-refl x'
  -- -- lemma-triIneq-3 {x} x' (inj₂ x≤0) = ≤-begin
  -- --                                       x
  -- --                                     ≤⟨ x' , x≤0 ⟩
  -- --                                       0#
  -- --                                     ≤⟨ 0' , ≤-‿reverse x' x≤0 ⟩
  -- --                                       - x
  -- --                                     ≤-∎⟨ -' x' ⟩
  -- -- lemma-triIneq-4 : {x : A} → F x → (x' : x ≥ 0# ⊎ x ≤ 0#) → - x ≤ ∣ x ∣ x'
  -- -- lemma-triIneq-4 {x} x' (inj₁ x≥0) = ≤-begin
  -- --                                       - x
  -- --                                     ≤⟨ -' x' , ≥-‿reverse x' x≥0 ⟩
  -- --                                       0#
  -- --                                     ≤⟨ 0' , x≥0 ⟩
  -- --                                       x
  -- --                                     ≤-∎⟨ x' ⟩
  -- -- lemma-triIneq-4 x' (inj₂ x≤0) = ≤-refl (-' x')
  -- --
  -- -- ∣∣-triangleIneq : {x y : A} → (x' : F x) → (y' : F y)
  -- --                 → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                 → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  --
  -- --                 → ∣ x + y ∣ (x' +'' y') ≤ (∣ x ∣ x'' + ∣ y ∣ y'')
  -- -- ∣∣-triangleIneq {x} {y} x' y' x'' y''
  -- --   = lemma-triIneq-1-1 (x' +' y') ((∣ x' ∣'  x'') +' (∣ y' ∣'  y'')) (x' +'' y') x+y≤∣x∣+∣y∣ -x-y≤∣x∣+∣y∣
  -- --     where x+y≤∣x∣+∣y∣ = ≤-begin
  -- --                         x + y
  -- --                       ≤⟨ x' +' y' , ≤+-compˡ x' (∣ x' ∣'  x'') y' (lemma-triIneq-3 x' x'') ⟩
  -- --                         (∣ x ∣ x'' + y)
  -- --                       ≤⟨ (∣ x' ∣'  x'') +' y' , ≤+-compʳ y' (∣ y' ∣'  y'') (∣ x' ∣'  x'') (lemma-triIneq-3 y' y'') ⟩
  -- --                         (∣ x ∣ x'' + ∣ y ∣ y'')
  -- --                       ≤-∎⟨ (∣ x' ∣'  x'') +' (∣ y' ∣'  y'') ⟩
  -- --           -x-y≤∣x∣+∣y∣ = ≤-begin
  -- --                         - (x + y)
  -- --                       ≈≤⟨ -' (x' +' y') , -‿distrib x' y' ⟩
  -- --                         (- x) + (- y)
  -- --                       ≤⟨ (-' x') +' (-' y') , ≤+-compˡ (-' x') (∣ x' ∣'  x'') (-' y') (lemma-triIneq-4 x' x'') ⟩
  -- --                         ∣ x ∣ x'' + (- y)
  -- --                       ≤⟨ ∣ x' ∣'  x'' +' (-' y') , ≤+-compʳ (-' y') (∣ y' ∣'  y'') (∣ x' ∣'  x'') (lemma-triIneq-4 y' y'') ⟩
  -- --                         ∣ x ∣ x'' + ∣ y ∣ y''
  -- --                       ≤-∎⟨ (∣ x' ∣'  x'') +' (∣ y' ∣'  y'') ⟩
  -- -- -- triangleIneq' : {x y : A} → F x → F y
  -- -- --                 → ∣ ∣ x ∣ + (- ∣ y ∣) ∣ ≤ (∣ x + (- y) ∣)
  -- --
  -- --
  -- -- -----------------------------------------------------------------------------
  -- -- -- distance
  -- --
  -- -- d-sign : {x : A} → {y : A} → F x × F y
  -- --         → (x' : x ≥ 0# ⊎ x ≤ 0#)
  -- --         → (y' : y ≥ 0# ⊎ y ≤ 0#)
  -- --         → (x + (- y)) ≥ 0# ⊎ (x + (- y)) ≤ 0#
  -- -- d-sign {x} {y} (x' , y') (inj₁ x≥0) (inj₂ y≤0) = (inj₁ (prop-1-1-2-xii-5 x' (-' y') x≥0 (≤-‿reverse y' y≤0)))
  -- -- d-sign {x} {y} (x' , y') (inj₂ x≤0) (inj₁ y≥0) = (inj₂ (prop-1-1-2-xii-6 x' (-' y') x≤0 (≥-‿reverse y' y≥0)))
  -- -- d-sign {x} {y} (x' , y') _          _          = x' +-sign (-' y') -- undicided
  -- -- -- d'' {x} {y} (x' , y') (inj₁ x≥0) (inj₁ y≥0)
  -- -- --   = [ ( λ x≤y → inj₂ (
  -- -- --           ≤-begin
  -- -- --             x + (- y)
  -- -- --           ≤≈⟨ x' +' (-' y') , ≤+-compˡ x' y' (-' y') x≤y ⟩
  -- -- --             y + (- y)
  -- -- --           ≈⟨ y' +' (-' y') , -‿inverseʳ y' ⟩
  -- -- --             0#
  -- -- --           ∎⟨ 0' ⟩
  -- -- --         )
  -- -- --       )
  -- -- --     , ( λ x≥y → inj₁ (
  -- -- --           ≤-begin
  -- -- --             0#
  -- -- --           ≈≤˘⟨ 0' , -‿inverseʳ y' ⟩
  -- -- --             y + (- y)
  -- -- --           ≤⟨ y' +' (-' y') , ≤+-compˡ y' x' (-' y') x≥y ⟩
  -- -- --             x + (- y)
  -- -- --           ≤-∎⟨ x' +' (-' y') ⟩
  -- -- --         )
  -- -- --       )
  -- -- --     ] (≤-connex x' y')
  -- -- -- d'' {x} {y} (x' , y') (inj₂ x≤0) (inj₂ y≤0)
  -- -- --   = [ ( λ -x≤-y → inj₁ (
  -- -- --           ≤-begin
  -- -- --             0#
  -- -- --           ≈≤˘⟨ 0' , -‿inverseʳ x' ⟩
  -- -- --             x + (- x)
  -- -- --           ≤⟨ x' +' (-' x') , ≤+-compʳ (-' x') (-' y') x' -x≤-y ⟩
  -- -- --             x + (- y)
  -- -- --           ≤-∎⟨ x' +' (-' y') ⟩
  -- -- --         )
  -- -- --       )
  -- -- --     , (λ -x≥-y → inj₂ (
  -- -- --           ≤-begin
  -- -- --             x + (- y)
  -- -- --           ≤≈⟨ x' +' (-' y') , ≤+-compʳ (-' y') (-' x') x' -x≥-y ⟩
  -- -- --             x + (- x)
  -- -- --           ≈⟨ x' +' (-' x') , -‿inverseʳ x' ⟩
  -- -- --             0#
  -- -- --           ∎⟨ 0' ⟩
  -- -- --         )
  -- -- --       )
  -- -- --     ] (≤-connex (-' x') (-' y'))
  -- --
  -- -- d : {x y : A} → F x × F y
  -- --     → (x ≥ 0# ⊎ x ≤ 0#)
  -- --     → (y ≥ 0# ⊎ y ≤ 0#)
  -- --     → A
  -- -- d {x} {y} (x' , y') x'' y'' = ∣ x + (- y) ∣ (d-sign (x' , y') x'' y'')
  -- --
  -- -- d-close : {x y : A} → (x' : F x) → (y' : F y)
  -- --         → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --         → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- --         → F (d (x' , y') x'' y'')
  -- -- d-close x' y' x'' y'' = ∣ (x' +' (-' y')) ∣' (d-sign (x' , y') x'' y'')
  -- --
  -- -- private
  -- --   d'' : {x : A} → {y : A} → F x × F y
  -- --           → (x' : x ≥ 0# ⊎ x ≤ 0#)
  -- --           → (y' : y ≥ 0# ⊎ y ≤ 0#)
  -- --           → (x + (- y)) ≥ 0# ⊎ (x + (- y)) ≤ 0#
  -- --   d'' = d-sign
  -- --   d' : {x y : A} → (x' : F x) → (y' : F y)
  -- --           → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --           → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- --           → F (d (x' , y') x'' y'')
  -- --   d' = d-close
  -- --
  -- -- prop-1-1-6-i : {x y : A} → (x' : F x) → (y' : F y)
  -- --               → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --               → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- --               → 0# ≤ d (x' , y') x'' y''
  -- -- prop-1-1-6-i x' y' x'' y'' = prop-1-1-5-i (x' +' -' y') (d'' (x' , y') x'' y'')
  -- --
  -- -- postulate
  -- --   prop-1-1-6-ii-1 : {x y : A} → (x' : F x) → (y' : F y)
  -- --                 → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                 → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- --                 → (d (x' , y') x'' y'' ≈ 0#)
  -- --                 → (x ≈ y)
  -- --   prop-1-1-6-ii-2 : {x y : A} → (x' : F x) → (y' : F y)
  -- --                 → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                 → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- --                 → (x ≈ y)
  -- --                 → (d (x' , y') x'' y'' ≈ 0#)
  -- --
  -- --
  -- -- prop-1-1-6-ii : {x y : A} → (x' : F x) → (y' : F y)
  -- --                 → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                 → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- --                 → (d (x' , y') x'' y'' ≈ 0#) ↔ (x ≈ y)
  -- -- prop-1-1-6-ii x' y' x'' y''
  -- --   = (prop-1-1-6-ii-1 x' y' x'' y'' , prop-1-1-6-ii-2 x' y' x'' y'')
  -- --
  -- -- -- prop-1-1-6-iii : {x y : A} → (x' : F x) → (y' : F y)
  -- -- --                 → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- -- --                 → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- -- --                 → d (x' , y') x'' y'' ≈ d (y' , x') y'' x''
  -- -- -- prop-1-1-6-iii {x} {y} x' y' x'' y''
  -- -- --   = [ (λ x-y≥0 → begin
  -- -- --               x + (- y)
  -- -- --             ≈⟨ x' +' (-' y') , +-comm x' (-' y') ⟩
  -- -- --               (- y) + x
  -- -- --             ≈˘⟨ (-' y') +' x' , +-congʳ (-' (-' x')) x' (-' y') (-‿doubleInverse x') ⟩
  -- -- --               (- y) + (- (- x))
  -- -- --             ≈˘⟨ (-' y') +' (-' (-' x')) , -‿distrib y' (-' x') ⟩
  -- -- --               - (y + (- x))
  -- -- --             ∎⟨ -' (y' +' (-' x')) ⟩)
  -- -- --     , (λ x-y≤0 → begin
  -- -- --               - (x + (- y))
  -- -- --             ≈⟨ -' (x' +' (-' y')) , -‿distrib x' (-' y') ⟩
  -- -- --               (- x) + (- (- y))
  -- -- --             ≈⟨ (-' x') +' (-' (-' y')) , +-congʳ (-' (-' y')) y' (-' x') (-‿doubleInverse y') ⟩
  -- -- --               (- x) + y
  -- -- --             ≈⟨ (-' x') +' y' , +-comm (-' x') y' ⟩
  -- -- --               y + (- x)
  -- -- --             ∎⟨ y' +' (-' x') ⟩)
  -- -- --     ] (d'' (x' , y') x'' y'')
  -- --
  -- -- lemma-d-triIneq : {x y z : A} → F x → F y → F z
  -- --                   → (x + y) ≈ ((x + (- z)) + (z + y))
  -- -- lemma-d-triIneq {x} {y} {z} x' y' z'
  -- --   = begin
  -- --     x + y
  -- --   ≈˘⟨ x' +' y' , +-congʳ (0' +' y') y' x' (0-identityˡ y') ⟩
  -- --     x + (0# + y)
  -- --   ≈˘⟨ x' +' (0' +' y') , +-congʳ (((-' z') +' z') +' y') (0' +' y') x' (+-congˡ ((-' z') +' z') 0' y' (-‿inverseˡ z')) ⟩
  -- --     x + (((- z) + z) + y)
  -- --   ≈⟨ x' +' (((-' z') +' z') +' y') , +-congʳ (((-' z') +' z') +' y') ((-' z') +' (z' +' y')) x' (+-assoc (-' z') z' y') ⟩
  -- --     x + ((- z) + (z + y))
  -- --   ≈˘⟨ x' +' ((-' z') +' (z' +' y')) , +-assoc x' (-' z') (z' +' y') ⟩
  -- --     (x + (- z)) + (z + y)
  -- --   ∎⟨ (x' +' (-' z')) +' (z' +' y') ⟩
  -- --
  -- -- d-triangleIneq : {x y z : A}
  -- --                → (x' : F x) → (y' : F y)→ (z' : F z)
  -- --                → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  -- --                → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  -- --                → (z'' : z ≥ 0# ⊎ z ≤ 0#)
  -- --                → d (x' , y') x'' y''
  -- --                  ≤ (d (x' , z') x'' z''
  -- --                    + d (z' , y') z'' y'')
  -- -- d-triangleIneq {x} {y} {z} x' y' z' x'' y'' z-sign
  -- --   = ≤-begin
  -- --     d (x' , y') x'' y''
  -- --   ≈≤⟨ d' x' y' x'' y'' , ∣∣-cong (x' +' (-' y')) ((x' +' (-' z')) +' (z' +' (-' y'))) (d'' (x' , y') x'' y'') ((x' +' (-' z')) +'' (z' +' (-' y'))) x-y≈x-z+z-y ⟩
  -- --     ∣ (x + (- z)) + (z + (- y)) ∣ ((x' +' (-' z')) +'' (z' +' (-' y')))
  -- --   ≤⟨ ∣ ((x' +' (-' z')) +' (z' +' (-' y'))) ∣' ((x' +' (-' z')) +'' (z' +' (-' y'))) , ∣∣-triangleIneq (x' +' (-' z')) (z' +' (-' y')) (d'' (x' , z') x'' z-sign) (d'' (z' , y') z-sign y'') ⟩
  -- --     (d (x' , z') x'' z-sign
  -- --     + d (z' , y') z-sign y'')
  -- --   ≤-∎⟨ d' x' z' x'' z-sign +' d' z' y' z-sign y'' ⟩
  -- --   where x-y≈x-z+z-y = (lemma-d-triIneq x' (-' y') z')
  -- --
  -- --
  -- -- -----------------------------------------------------------------------------
  -- -- -- convergence
  -- --
  -- -- lim_≈_ : {x : ℕ → A} → (x' : (n : ℕ) → F (x n))
  -- --         → {a : A} → F a → Set
  -- -- lim x' ≈ a' = {ε : A} → F ε → ε ≥ 0#
  -- --                 → Σ[ N ∈ ℕ ] (
  -- --                     {n : ℕ} → n ≥ᴺ N
  -- --                     → (d (x' n , a') (sign (x' n)) (sign a'))
  -- --                       < ε
  -- --                   )
  -- -- --
  -- -- -- postulate
  -- -- sandwich-lemma : {x y z : ℕ → A}
  -- --                → {x' : (n : ℕ) → F (x n)}
  -- --                → {y' : (n : ℕ) → F (y n)}
  -- --                → {z' : (n : ℕ) → F (z n)}
  -- --                → {a : A} → {a' : F a}
  -- --                → lim x' ≈ a' → lim y' ≈ a'
  -- --                → (Σ[ Nx₀ ∈ ℕ ] ({n : ℕ} → n ≥ᴺ Nx₀ → (x n ≤ z n)))
  -- --                → (Σ[ Ny₀ ∈ ℕ ] ({n : ℕ} → n ≥ᴺ Ny₀ → (z n ≤ y n)))
  -- --                → lim z' ≈ a'
  -- -- sandwich-lemma {x} {y} {z} {x'} {y'} {z'} {a} {a'}
  -- --   limx≈a limy≈a (Nx₀ , xn≤zn) (Ny₀ , zn≤yn) {ε} ε∈F ε≥0
  -- --   = (N , n≥N→∣zn-a∣<ε)
  -- --     where Nx₁ = proj₁ (limx≈a ε∈F ε≥0)
  -- --           Ny₁ = proj₁ (limy≈a ε∈F ε≥0)
  -- --           N = maxᴺ Nx₀ (Ny₀ ∷ Nx₁ ∷ Ny₁ ∷ [])
  -- --           N≥Nx₀∷Ny₀∷Nx₁∷Ny₁ = max-order Nx₀ (Ny₀ ∷ Nx₁ ∷ Ny₁ ∷ [])
  -- --           N≥Nx₀ = proj₁ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁
  -- --           N≥Ny₀ = proj₁ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁)
  -- --           N≥Nx₁ = proj₁ (proj₂ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁))
  -- --           N≥Ny₁ = proj₁ (proj₂ (proj₂ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁)))
  -- --           n≥N→n≥Nx₀ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Nx₀} {N} {n} N≥Nx₀ n≥N)
  -- --           n≥N→n≥Ny₀ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Ny₀} {N} {n} N≥Ny₀ n≥N)
  -- --           n≥N→n≥Nx₁ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Nx₁} {N} {n} N≥Nx₁ n≥N)
  -- --           n≥N→n≥Ny₁ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Ny₁} {N} {n} N≥Ny₁ n≥N)
  -- --           -- -ε < xn - a ≤ zn - a ≤ yn - a < ε
  -- --           n≥N→xn-a≤zn-a = λ {n} → λ n≥N → ≤+-compˡ (x' n) (z' n) (-' a') (xn≤zn {n} (n≥N→n≥Nx₀ n≥N))
  -- --           n≥N→zn-a≤yn-a = λ {n} → λ n≥N → ≤+-compˡ (z' n) (y' n) (-' a') (zn≤yn {n} (n≥N→n≥Ny₀ n≥N))
  -- --           n≥N→∣xn-a∣<ε = proj₂ (limx≈a ε∈F ε≥0)
  -- --           n≥N→∣yn-a∣<ε = proj₂ (limy≈a ε∈F ε≥0)
  -- --           n≥N→-xn+a<ε = λ {n} → λ n≥N → proj₂ (lemma-triIneq-1-2' (x' n +' (-' a')) ε∈F (d'' (x' n , a') (sign (x' n)) (sign a')) (n≥N→∣xn-a∣<ε (n≥N→n≥Nx₁ n≥N)))
  -- --           n≥N→-ε<xn-a = λ {n : ℕ} → λ n≥N → <-‿moveˡ (x' n +' (-' a')) ε∈F (n≥N→-xn+a<ε n≥N)
  -- --           n≥N→yn-a<ε = λ {n} → λ n≥N → proj₁ (lemma-triIneq-1-2' (y' n +' (-' a')) ε∈F (d'' (y' n , a') (sign (y' n)) (sign a')) (n≥N→∣yn-a∣<ε (n≥N→n≥Ny₁ n≥N)))
  -- --           n≥N→-ε<zn-a = λ {n} → λ n≥N → <≤-trans (-' ε∈F) (x' n +' (-' a')) (z' n +' (-' a')) (n≥N→-ε<xn-a n≥N) (n≥N→xn-a≤zn-a n≥N)
  -- --           n≥N→zn-a<ε = λ {n} → λ n≥N → ≤<-trans (z' n +' (-' a')) (y' n +' (-' a')) ε∈F (n≥N→zn-a≤yn-a n≥N) (n≥N→yn-a<ε n≥N)
  -- --           n≥N→∣zn-a∣<ε = λ {n} → λ n≥N → lemma-triIneq-2-1' (z' n +' (-' a')) ε∈F (d'' ((z' n , a')) (sign (z' n)) (sign a')) (n≥N→zn-a<ε n≥N) (n≥N→-ε<zn-a n≥N)
  -- -- -- postulate
  -- -- --   prop-1-2-3 : {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
  -- -- --              → {a lb ub : A} → {a' : F a}
  -- -- --              → lim x' ≈ a'
  -- -- --              → ((n : ℕ) → lb ≤ x n × x n ≤ ub)
  -- -- --              → lb ≤ a × a ≤ ub
  -- -- --   -- prop-1-2-3 {x} {x'} {a} {a'} limx≈a n→lb≤xn≤ub
  -- -- --   --   = (? , ?)
  -- -- --   -- prop-1-2-5
  -- -- --   lim-unique : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  -- -- --              → {a b : A} {a' : F a} {b' : F b}
  -- -- --              → lim x' ≈ a' → lim x' ≈ b'
  -- -- --              → a ≈ b
  -- -- --   -- lim-unique {x} {x'} {a} {b} {a'} {b'} limx≈a limx≈b
  -- -- --   --   = ?
  -- --
  -- -- _+ᶠᵘⁿᶜ_ : {B : Set} (x y : B → A) → B → A
  -- -- (x +ᶠᵘⁿᶜ y) n = x n + y n
  -- -- _+'ᶠᵘⁿᶜ_ : {B : Set} {x y : B → A}
  -- --            (x' : (b : B) → F (x b))
  -- --            (y' : (b : B) → F (y b))
  -- --           → (b : B) → F (x b + y b)
  -- -- (x' +'ᶠᵘⁿᶜ y') b = x' b +' y' b
  -- --
  -- -- _*ᶠᵘⁿᶜ_ : {B : Set} (x y : B → A) → B → A
  -- -- (x *ᶠᵘⁿᶜ y) n = x n * y n
  -- -- _*'ᶠᵘⁿᶜ_ : {B : Set} {x y : B → A}
  -- --            (x' : (b : B) → F (x b))
  -- --            (y' : (b : B) → F (y b))
  -- --          → (b : B) → F (x b * y b)
  -- -- (x' *'ᶠᵘⁿᶜ y') b = x' b *' y' b
  -- --
  -- -- const : {B : Set} → A → B → A
  -- -- const c _ = c
  -- --
  -- -- postulate
  -- --   _/ᶠᵘⁿᶜ_ : {B : Set} (x : B → A)
  -- --           → {y : B → A} (y\[0] : (b : B) → (F \[ _≈ 0# ]) (y b))
  -- --           → B → A
  -- -- --(x /ᶠᵘⁿᶜ y\[0]) b = x b * (y b)
  -- --
  -- -- const' : {B : Set} → {c : A} → F c → B → F c
  -- -- const' c' _ = c'
  -- --
  -- -- postulate
  -- --   +-limit-homo : {x y : ℕ → A}
  -- --                  {x' : (n : ℕ) → F (x n)}
  -- --                  {y' : (n : ℕ) → F (y n)}
  -- --                  {a b : A} {a' : F a} {b' : F b}
  -- --                → lim x' ≈ a' → lim y' ≈ b'
  -- --                → lim (x' +'ᶠᵘⁿᶜ y') ≈ (a' +' b')
  -- --   *-limit-homo : {x y : ℕ → A}
  -- --                  {x' : (n : ℕ) → F (x n)}
  -- --                  {y' : (n : ℕ) → F (y n)}
  -- --                  {a b : A} {a' : F a} {b' : F b}
  -- --                → lim x' ≈ a' → lim y' ≈ b'
  -- --                → lim (x' *'ᶠᵘⁿᶜ y' ) ≈ (a' *' b')
  -- --   const*-limit-homo : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  -- --                       {a c : A} {a' : F a} {c' : F c}
  -- --                     → lim x' ≈ a'
  -- --                     → lim (const' c' *'ᶠᵘⁿᶜ x') ≈ (c' *' a')
  -- --   -- const*-limit-homo {x} {x'} {a} {c} {a'} {c'} limx'≈a'
  -- --   --   = ?
  -- --   -- /-limit-homo : {x y : ℕ → A}
  -- --   --               {x' : (n : ℕ) → F (x n)}
  -- --   --               {y'\[0] : (n : ℕ) → (F \[ _≈ 0# ]) (y n)}
  -- --   --               → {a b : A}
  -- --   --               → ((n : ℕ) → ¬ (y n ≈ 0#)) → ¬ (b ≈ 0#)
  -- --   --               → lim x ≈ a → lim y ≈ b
  -- --   --               → lim (λ n → x n / y n) ≈ (a / b)
  -- --
  -- -- _Convergent : {x : ℕ → A} (x' : (n : ℕ) → F (x n)) → Set
  -- -- x' Convergent = Σ[ a ∈ A ] (Σ[ a' ∈ F a ] (lim x' ≈ a'))
  -- --
  -- --
  -- -- -----------------------------------------------------------------------------
  -- -- -- MonotoneSequeceProperty
  -- --
  -- -- _Bounded : {B : Set} (x : B → A) → Set
  -- -- _Bounded {B} x = Σ[ b ∈ A ] (
  -- --                   Σ[ b' ∈ F b ] (
  -- --                     (n : B) → (x n) ≤ b
  -- --                   )
  -- --                 )
  -- -- postulate
  -- --   prop-1-2-5 : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  -- --                {a b : A} {a' : F a} {b' : F b}
  -- --               → lim x' ≈ a' → lim x' ≈ b'
  -- --               → a ≈ b
  -- --   convergent⇒bounded : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  -- --                       → x' Convergent → x Bounded
  -- -- -- convergent⇒bounded {x} {x'} (a , a' , limx≈a)
  -- -- --   = (? , ? , ?)
  -- --
  -- -- _Increasing : (x : ℕ → A) → Set
  -- -- x Increasing = (n m : ℕ) → (n ≤ᴺ m) → (x n ≤ x m)
  -- --
  -- --
  -- -- MonotoneSequeceProperty : Set
  -- -- MonotoneSequeceProperty = {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
  -- --                           → x Increasing → x Bounded
  -- --                           → x' Convergent
  -- --
  -- -- -----------------------------------------------------------------------------
  -- -- -- Cauchy Completeness
  -- --
  -- -- _Cauchy : {x : ℕ → A} → (x' : (n : ℕ) → F (x n)) → Set
  -- -- x' Cauchy = (ε : A) → F ε → ε ≥ 0#
  -- --           → Σ[ N ∈ ℕ ] (
  -- --               (m n : ℕ) → m ≥ᴺ N → n ≥ᴺ N
  -- --               → (d (x' m , x' n) (sign (x' m)) (sign (x' n))) < ε
  -- --             )
  -- --
  -- -- CauchyComplete : Set
  -- -- CauchyComplete = {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
  -- --                 → x' Cauchy → x' Convergent
  -- --
  -- -- -----------------------------------------------------------------------------
  -- -- -- least-upper-bound property
  -- --
  -- -- _IsUpperBoundFor_ : {b : A} → F b → (S : A → Set) → Set
  -- -- _IsUpperBoundFor_ {b} b' S = {x : A} → F x → S x → x ≤ b
  -- --
  -- -- BoundedAbove : (S : A → Set) → Set
  -- -- BoundedAbove S = Σ[ b ∈ A ] Σ[ b' ∈ F b ] (b' IsUpperBoundFor S)
  -- --
  -- -- _≈sup_ : {b : A} → (F b) → (S : A → Set) → Set
  -- -- _≈sup_ {b} b' S = (b' IsUpperBoundFor S)
  -- --                   × ({a : A} {a' : F a}
  -- --                       → (a' IsUpperBoundFor S) → b ≤ a)
  -- --
  -- -- lemma-1-3-2-⇒ : {b : A} {b' : F b} {S : A → Set}
  -- --               → S IsNonEmpty
  -- --               → Σ[ ε ∈ A ] (F ε) × (ε > 0#)
  -- --                 × ({x : A} → F x → S x → (x ≤ (b + (- ε))))
  -- --               → ¬ (b' ≈sup S)
  -- -- lemma-1-3-2-⇒ {b} {b'} {S} (x , x∈S)
  -- --   (ε , ε' , (ε≥0 , ε≉0) , b-ε-isUpperBound)
  -- --   (b-isUpperBound , b-isLeast)
  -- --   = b≉b b≈b
  -- --   where b≤b-ε = b-isLeast {b + (- ε)} {b' +' (-' ε')} b-ε-isUpperBound
  -- --         b-ε≤b = ≤≈-trans (b' +' (-' ε')) (b' +' 0') b' (≤+-compʳ (-' ε') 0' b' (≥-‿reverse ε' ε≥0)) ((b' 0-identityʳ))
  -- --         b-ε≉b = λ b-ε≈b → ε≉0 (lemma-1-1-5-ii-2 ε' (+-cancelˡ (-' ε') 0' b' (≈-trans (b' +' (-' ε')) b' (b' +' 0') b-ε≈b (≈-sym (b' +' 0') b' (b' 0-identityʳ)))))
  -- --         b<b = ≤<-trans b' (b' +' (-' ε')) b' b≤b-ε (b-ε≤b , b-ε≉b)
  -- --         b≉b = proj₂ b<b
  -- --         b≈b = ≈-refl b'
  -- -- -- use of nonemptyness ?
  -- --
  -- -- lemma-1-3-2-1 : {a b : A} → F a → F b
  -- --                 → a < b → (b + (- a)) > 0#
  -- -- lemma-1-3-2-1 {a} {b} a' b' (a≤b , a≉b) = b-a≥0 , b-a≉0
  -- --   where b-a≥0 = ≤-begin
  -- --                   0#
  -- --                 ≈≤˘⟨ 0' , -‿inverseʳ a' ⟩
  -- --                   a + (- a)
  -- --                 ≤⟨ a' +' (-' a') , ≤+-compˡ a' b' (-' a') a≤b ⟩
  -- --                   b + (- a)
  -- --                 ≤-∎⟨ b' +' (-' a') ⟩
  -- --         b-a≉0 = λ b-a≈0 → a≉b (
  -- --                             begin
  -- --                               a
  -- --                             ≈˘⟨ a' , -‿doubleInverse a' ⟩
  -- --                               - (- a)
  -- --                             ≈˘⟨ -' (-' a') , -‿uniqueˡ b' (-' a') b-a≈0 ⟩
  -- --                               b
  -- --                             ∎⟨ b' ⟩
  -- --                           )
  -- --
  -- -- lemma-1-3-2-⇐ : {b : A} {b' : F b} {S : A → Set}
  -- --              → S IsNonEmpty
  -- --              → b' IsUpperBoundFor S
  -- --              → Σ[ a ∈ A ]
  -- --                 Σ[ a' ∈ F a ]
  -- --                   (a' IsUpperBoundFor S)
  -- --                   × a < b
  -- --              → Σ[ ε ∈ A ] (F ε) × (ε > 0#)
  -- --                × ({x : A} → F x → S x → (x ≤ (b + (- ε))))
  -- -- lemma-1-3-2-⇐ {b} {b'} {S} (s , s∈S) b-isUpperBound
  -- --   (a , a' , a-isUpperBound , (a≤b , a≉b))
  -- --   = ((b + (- a)) , ((b' +' (-' a'))) , b-a>0 , ∀x∈S→x≤b-b+a)
  -- --   where b-a>0 = lemma-1-3-2-1 a' b' ((a≤b , a≉b))
  -- --         ∀x∈S→x≤b-b+a = λ {x} → λ x' → λ x∈S
  -- --                          → ≤-begin
  -- --                             x
  -- --                           ≤≈⟨ x' , a-isUpperBound x' x∈S ⟩
  -- --                             a
  -- --                           ≈˘⟨ a' , 0-identityˡ a' ⟩
  -- --                             0# + a
  -- --                           ≈˘⟨ 0' +' a' , +-congˡ (b' +' (-' b')) 0' a' (-‿inverseʳ b') ⟩
  -- --                             (b + (- b)) + a
  -- --                           ≈⟨ (b' +' (-' b')) +' a' , +-assoc b' (-' b') a' ⟩
  -- --                             b + ((- b) + a)
  -- --                           ≈˘⟨ b' +' ((-' b') +' a') , +-congʳ ((-' b') +' (-' (-' a'))) ((-' b') +' a') b' (+-congʳ (-' (-' a')) a' (-' b') (-‿doubleInverse a')) ⟩
  -- --                             b + ((- b) + (- (- a)))
  -- --                           ≈˘⟨ b' +' ((-' b') +' (-' (-' a'))) , +-congʳ (-' (b' +' (-' a'))) ((-' b') +' (-' (-' a'))) b' (-‿distrib b' (-' a')) ⟩
  -- --                             b + (- (b + (- a)))
  -- --                           ∎⟨ b' +' (-' (b' +' (-' a'))) ⟩
  -- --                 → d (x' , y') x'' y'' ≈ d (y' , x') y'' x''
  -- -- prop-1-1-6-iii {x} {y} x' y' x'' y''
  -- --   = [ (λ x-y≥0 → begin
  -- --               x + (- y)
  -- --             ≈⟨ x' +' (-' y') , +-comm x' (-' y') ⟩
  -- --               (- y) + x
  -- --             ≈˘⟨ (-' y') +' x' , +-congʳ (-' (-' x')) x' (-' y') (-‿doubleInverse x') ⟩
  -- --               (- y) + (- (- x))
  -- --             ≈˘⟨ (-' y') +' (-' (-' x')) , -‿distrib y' (-' x') ⟩
  -- --               - (y + (- x))
  -- --             ∎⟨ -' (y' +' (-' x')) ⟩)
  -- --     , (λ x-y≤0 → begin
  -- --               - (x + (- y))
  -- --             ≈⟨ -' (x' +' (-' y')) , -‿distrib x' (-' y') ⟩
  -- --               (- x) + (- (- y))
  -- --             ≈⟨ (-' x') +' (-' (-' y')) , +-congʳ (-' (-' y')) y' (-' x') (-‿doubleInverse y') ⟩
  -- --               (- x) + y
  -- --             ≈⟨ (-' x') +' y' , +-comm (-' x') y' ⟩
  -- --               y + (- x)
  -- --             ∎⟨ y' +' (-' x') ⟩)
  -- --     ] (d'' (x' , y') x'' y'')
  --
  -- lemma-d-triIneq : {x y z : A} → F x → F y → F z
  --                   → (x + y) ≈ ((x + (- z)) + (z + y))
  -- lemma-d-triIneq {x} {y} {z} x' y' z'
  --   = begin
  --     x + y
  --   ≈˘⟨ x' +' y' , +-congʳ (0' +' y') y' x' (0-identityˡ y') ⟩
  --     x + (0# + y)
  --   ≈˘⟨ x' +' (0' +' y') , +-congʳ (((-' z') +' z') +' y') (0' +' y') x' (+-congˡ ((-' z') +' z') 0' y' (-‿inverseˡ z')) ⟩
  --     x + (((- z) + z) + y)
  --   ≈⟨ x' +' (((-' z') +' z') +' y') , +-congʳ (((-' z') +' z') +' y') ((-' z') +' (z' +' y')) x' (+-assoc (-' z') z' y') ⟩
  --     x + ((- z) + (z + y))
  --   ≈˘⟨ x' +' ((-' z') +' (z' +' y')) , +-assoc x' (-' z') (z' +' y') ⟩
  --     (x + (- z)) + (z + y)
  --   ∎⟨ (x' +' (-' z')) +' (z' +' y') ⟩
  --
  -- d-triangleIneq : {x y z : A}
  --                → (x' : F x) → (y' : F y)→ (z' : F z)
  --                → (x'' : x ≥ 0# ⊎ x ≤ 0#)
  --                → (y'' : y ≥ 0# ⊎ y ≤ 0#)
  --                → (z'' : z ≥ 0# ⊎ z ≤ 0#)
  --                → d (x' , y') x'' y''
  --                  ≤ (d (x' , z') x'' z''
  --                    + d (z' , y') z'' y'')
  -- d-triangleIneq {x} {y} {z} x' y' z' x'' y'' z-sign
  --   = ≤-begin
  --     d (x' , y') x'' y''
  --   ≈≤⟨ d' x' y' x'' y'' , ∣∣-cong (x' +' (-' y')) ((x' +' (-' z')) +' (z' +' (-' y'))) (d'' (x' , y') x'' y'') ((x' +' (-' z')) +'' (z' +' (-' y'))) x-y≈x-z+z-y ⟩
  --     ∣ (x + (- z)) + (z + (- y)) ∣ ((x' +' (-' z')) +'' (z' +' (-' y')))
  --   ≤⟨ ∣ ((x' +' (-' z')) +' (z' +' (-' y'))) ∣' ((x' +' (-' z')) +'' (z' +' (-' y'))) , ∣∣-triangleIneq (x' +' (-' z')) (z' +' (-' y')) (d'' (x' , z') x'' z-sign) (d'' (z' , y') z-sign y'') ⟩
  --     (d (x' , z') x'' z-sign
  --     + d (z' , y') z-sign y'')
  --   ≤-∎⟨ d' x' z' x'' z-sign +' d' z' y' z-sign y'' ⟩
  --   where x-y≈x-z+z-y = (lemma-d-triIneq x' (-' y') z')
  --
  --
  -- -----------------------------------------------------------------------------
  -- -- convergence
  --
  -- lim_≈_ : {x : ℕ → A} → (x' : (n : ℕ) → F (x n))
  --         → {a : A} → F a → Set
  -- lim x' ≈ a' = {ε : A} → F ε → ε ≥ 0#
  --                 → Σ[ N ∈ ℕ ] (
  --                     {n : ℕ} → n ≥ᴺ N
  --                     → (d (x' n , a') (sign (x' n)) (sign a'))
  --                       < ε
  --                   )
  -- --
  -- -- postulate
  -- sandwich-lemma : {x y z : ℕ → A}
  --                → {x' : (n : ℕ) → F (x n)}
  --                → {y' : (n : ℕ) → F (y n)}
  --                → {z' : (n : ℕ) → F (z n)}
  --                → {a : A} → {a' : F a}
  --                → lim x' ≈ a' → lim y' ≈ a'
  --                → (Σ[ Nx₀ ∈ ℕ ] ({n : ℕ} → n ≥ᴺ Nx₀ → (x n ≤ z n)))
  --                → (Σ[ Ny₀ ∈ ℕ ] ({n : ℕ} → n ≥ᴺ Ny₀ → (z n ≤ y n)))
  --                → lim z' ≈ a'
  -- sandwich-lemma {x} {y} {z} {x'} {y'} {z'} {a} {a'}
  --   limx≈a limy≈a (Nx₀ , xn≤zn) (Ny₀ , zn≤yn) {ε} ε∈F ε≥0
  --   = (N , n≥N→∣zn-a∣<ε)
  --     where Nx₁ = proj₁ (limx≈a ε∈F ε≥0)
  --           Ny₁ = proj₁ (limy≈a ε∈F ε≥0)
  --           N = maxᴺ Nx₀ (Ny₀ ∷ Nx₁ ∷ Ny₁ ∷ [])
  --           N≥Nx₀∷Ny₀∷Nx₁∷Ny₁ = max-order Nx₀ (Ny₀ ∷ Nx₁ ∷ Ny₁ ∷ [])
  --           N≥Nx₀ = proj₁ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁
  --           N≥Ny₀ = proj₁ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁)
  --           N≥Nx₁ = proj₁ (proj₂ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁))
  --           N≥Ny₁ = proj₁ (proj₂ (proj₂ (proj₂ N≥Nx₀∷Ny₀∷Nx₁∷Ny₁)))
  --           n≥N→n≥Nx₀ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Nx₀} {N} {n} N≥Nx₀ n≥N)
  --           n≥N→n≥Ny₀ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Ny₀} {N} {n} N≥Ny₀ n≥N)
  --           n≥N→n≥Nx₁ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Nx₁} {N} {n} N≥Nx₁ n≥N)
  --           n≥N→n≥Ny₁ = λ {n : ℕ} → λ n≥N → (≤ᴺ-trans {Ny₁} {N} {n} N≥Ny₁ n≥N)
  --           -- -ε < xn - a ≤ zn - a ≤ yn - a < ε
  --           n≥N→xn-a≤zn-a = λ {n} → λ n≥N → ≤+-compˡ (x' n) (z' n) (-' a') (xn≤zn {n} (n≥N→n≥Nx₀ n≥N))
  --           n≥N→zn-a≤yn-a = λ {n} → λ n≥N → ≤+-compˡ (z' n) (y' n) (-' a') (zn≤yn {n} (n≥N→n≥Ny₀ n≥N))
  --           n≥N→∣xn-a∣<ε = proj₂ (limx≈a ε∈F ε≥0)
  --           n≥N→∣yn-a∣<ε = proj₂ (limy≈a ε∈F ε≥0)
  --           n≥N→-xn+a<ε = λ {n} → λ n≥N → proj₂ (lemma-triIneq-1-2' (x' n +' (-' a')) ε∈F (d'' (x' n , a') (sign (x' n)) (sign a')) (n≥N→∣xn-a∣<ε (n≥N→n≥Nx₁ n≥N)))
  --           n≥N→-ε<xn-a = λ {n : ℕ} → λ n≥N → <-‿moveˡ (x' n +' (-' a')) ε∈F (n≥N→-xn+a<ε n≥N)
  --           n≥N→yn-a<ε = λ {n} → λ n≥N → proj₁ (lemma-triIneq-1-2' (y' n +' (-' a')) ε∈F (d'' (y' n , a') (sign (y' n)) (sign a')) (n≥N→∣yn-a∣<ε (n≥N→n≥Ny₁ n≥N)))
  --           n≥N→-ε<zn-a = λ {n} → λ n≥N → <≤-trans (-' ε∈F) (x' n +' (-' a')) (z' n +' (-' a')) (n≥N→-ε<xn-a n≥N) (n≥N→xn-a≤zn-a n≥N)
  --           n≥N→zn-a<ε = λ {n} → λ n≥N → ≤<-trans (z' n +' (-' a')) (y' n +' (-' a')) ε∈F (n≥N→zn-a≤yn-a n≥N) (n≥N→yn-a<ε n≥N)
  --           n≥N→∣zn-a∣<ε = λ {n} → λ n≥N → lemma-triIneq-2-1' (z' n +' (-' a')) ε∈F (d'' ((z' n , a')) (sign (z' n)) (sign a')) (n≥N→zn-a<ε n≥N) (n≥N→-ε<zn-a n≥N)
  -- -- postulate
  -- --   prop-1-2-3 : {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
  -- --              → {a lb ub : A} → {a' : F a}
  -- --              → lim x' ≈ a'
  -- --              → ((n : ℕ) → lb ≤ x n × x n ≤ ub)
  -- --              → lb ≤ a × a ≤ ub
  -- --   -- prop-1-2-3 {x} {x'} {a} {a'} limx≈a n→lb≤xn≤ub
  -- --   --   = (? , ?)
  -- --   -- prop-1-2-5
  -- --   lim-unique : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  -- --              → {a b : A} {a' : F a} {b' : F b}
  -- --              → lim x' ≈ a' → lim x' ≈ b'
  -- --              → a ≈ b
  -- --   -- lim-unique {x} {x'} {a} {b} {a'} {b'} limx≈a limx≈b
  -- --   --   = ?
  --
  -- _+ᶠᵘⁿᶜ_ : {B : Set} (x y : B → A) → B → A
  -- (x +ᶠᵘⁿᶜ y) n = x n + y n
  -- _+'ᶠᵘⁿᶜ_ : {B : Set} {x y : B → A}
  --            (x' : (b : B) → F (x b))
  --            (y' : (b : B) → F (y b))
  --           → (b : B) → F (x b + y b)
  -- (x' +'ᶠᵘⁿᶜ y') b = x' b +' y' b
  --
  -- _*ᶠᵘⁿᶜ_ : {B : Set} (x y : B → A) → B → A
  -- (x *ᶠᵘⁿᶜ y) n = x n * y n
  -- _*'ᶠᵘⁿᶜ_ : {B : Set} {x y : B → A}
  --            (x' : (b : B) → F (x b))
  --            (y' : (b : B) → F (y b))
  --          → (b : B) → F (x b * y b)
  -- (x' *'ᶠᵘⁿᶜ y') b = x' b *' y' b
  --
  -- const : {B : Set} → A → B → A
  -- const c _ = c
  --
  -- postulate
  --   _/ᶠᵘⁿᶜ_ : {B : Set} (x : B → A)
  --           → {y : B → A} (y\[0] : (b : B) → (F \[ _≈ 0# ]) (y b))
  --           → B → A
  -- --(x /ᶠᵘⁿᶜ y\[0]) b = x b * (y b)
  --
  -- const' : {B : Set} → {c : A} → F c → B → F c
  -- const' c' _ = c'
  --
  -- postulate
  --   +-limit-homo : {x y : ℕ → A}
  --                  {x' : (n : ℕ) → F (x n)}
  --                  {y' : (n : ℕ) → F (y n)}
  --                  {a b : A} {a' : F a} {b' : F b}
  --                → lim x' ≈ a' → lim y' ≈ b'
  --                → lim (x' +'ᶠᵘⁿᶜ y') ≈ (a' +' b')
  --   *-limit-homo : {x y : ℕ → A}
  --                  {x' : (n : ℕ) → F (x n)}
  --                  {y' : (n : ℕ) → F (y n)}
  --                  {a b : A} {a' : F a} {b' : F b}
  --                → lim x' ≈ a' → lim y' ≈ b'
  --                → lim (x' *'ᶠᵘⁿᶜ y' ) ≈ (a' *' b')
  --   const*-limit-homo : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  --                       {a c : A} {a' : F a} {c' : F c}
  --                     → lim x' ≈ a'
  --                     → lim (const' c' *'ᶠᵘⁿᶜ x') ≈ (c' *' a')
  --   -- const*-limit-homo {x} {x'} {a} {c} {a'} {c'} limx'≈a'
  --   --   = ?
  --   -- /-limit-homo : {x y : ℕ → A}
  --   --               {x' : (n : ℕ) → F (x n)}
  --   --               {y'\[0] : (n : ℕ) → (F \[ _≈ 0# ]) (y n)}
  --   --               → {a b : A}
  --   --               → ((n : ℕ) → ¬ (y n ≈ 0#)) → ¬ (b ≈ 0#)
  --   --               → lim x ≈ a → lim y ≈ b
  --   --               → lim (λ n → x n / y n) ≈ (a / b)
  --
  -- _Convergent : {x : ℕ → A} (x' : (n : ℕ) → F (x n)) → Set
  -- x' Convergent = Σ[ a ∈ A ] (Σ[ a' ∈ F a ] (lim x' ≈ a'))
  --
  --
  -- -----------------------------------------------------------------------------
  -- -- MonotoneSequeceProperty
  --
  -- _Bounded : {B : Set} (x : B → A) → Set
  -- _Bounded {B} x = Σ[ b ∈ A ] (
  --                   Σ[ b' ∈ F b ] (
  --                     (n : B) → (x n) ≤ b
  --                   )
  --                 )
  -- postulate
  --   prop-1-2-5 : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  --                {a b : A} {a' : F a} {b' : F b}
  --               → lim x' ≈ a' → lim x' ≈ b'
  --               → a ≈ b
  --   convergent⇒bounded : {x : ℕ → A} {x' : (n : ℕ) → F (x n)}
  --                       → x' Convergent → x Bounded
  -- -- convergent⇒bounded {x} {x'} (a , a' , limx≈a)
  -- --   = (? , ? , ?)
  --
  -- _Increasing : (x : ℕ → A) → Set
  -- x Increasing = (n m : ℕ) → (n ≤ᴺ m) → (x n ≤ x m)
  --
  --
  -- MonotoneSequeceProperty : Set
  -- MonotoneSequeceProperty = {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
  --                           → x Increasing → x Bounded
  --                           → x' Convergent
  --
  -- -----------------------------------------------------------------------------
  -- -- Cauchy Completeness
  --
  -- _Cauchy : {x : ℕ → A} → (x' : (n : ℕ) → F (x n)) → Set
  -- x' Cauchy = (ε : A) → F ε → ε ≥ 0#
  --           → Σ[ N ∈ ℕ ] (
  --               (m n : ℕ) → m ≥ᴺ N → n ≥ᴺ N
  --               → (d (x' m , x' n) (sign (x' m)) (sign (x' n))) < ε
  --             )
  --
  -- CauchyComplete : Set
  -- CauchyComplete = {x : ℕ → A} → {x' : (n : ℕ) → F (x n)}
  --                 → x' Cauchy → x' Convergent
  --
  -- -----------------------------------------------------------------------------
  -- -- least-upper-bound property
  --
  -- _IsUpperBoundFor_ : {b : A} → F b → (S : A → Set) → Set
  -- _IsUpperBoundFor_ {b} b' S = {x : A} → F x → S x → x ≤ b
  --
  -- BoundedAbove : (S : A → Set) → Set
  -- BoundedAbove S = Σ[ b ∈ A ] Σ[ b' ∈ F b ] (b' IsUpperBoundFor S)
  --
  -- _≈sup_ : {b : A} → (F b) → (S : A → Set) → Set
  -- _≈sup_ {b} b' S = (b' IsUpperBoundFor S)
  --                   × ({a : A} {a' : F a}
  --                       → (a' IsUpperBoundFor S) → b ≤ a)
  --
  -- lemma-1-3-2-⇒ : {b : A} {b' : F b} {S : A → Set}
  --               → S IsNonEmpty
  --               → Σ[ ε ∈ A ] (F ε) × (ε > 0#)
  --                 × ({x : A} → F x → S x → (x ≤ (b + (- ε))))
  --               → ¬ (b' ≈sup S)
  -- lemma-1-3-2-⇒ {b} {b'} {S} (x , x∈S)
  --   (ε , ε' , (ε≥0 , ε≉0) , b-ε-isUpperBound)
  --   (b-isUpperBound , b-isLeast)
  --   = b≉b b≈b
  --   where b≤b-ε = b-isLeast {b + (- ε)} {b' +' (-' ε')} b-ε-isUpperBound
  --         b-ε≤b = ≤≈-trans (b' +' (-' ε')) (b' +' 0') b' (≤+-compʳ (-' ε') 0' b' (≥-‿reverse ε' ε≥0)) ((b' 0-identityʳ))
  --         b-ε≉b = λ b-ε≈b → ε≉0 (lemma-1-1-5-ii-2 ε' (+-cancelˡ (-' ε') 0' b' (≈-trans (b' +' (-' ε')) b' (b' +' 0') b-ε≈b (≈-sym (b' +' 0') b' (b' 0-identityʳ)))))
  --         b<b = ≤<-trans b' (b' +' (-' ε')) b' b≤b-ε (b-ε≤b , b-ε≉b)
  --         b≉b = proj₂ b<b
  --         b≈b = ≈-refl b'
  -- -- use of nonemptyness ?
  --
  -- lemma-1-3-2-1 : {a b : A} → F a → F b
  --                 → a < b → (b + (- a)) > 0#
  -- lemma-1-3-2-1 {a} {b} a' b' (a≤b , a≉b) = b-a≥0 , b-a≉0
  --   where b-a≥0 = ≤-begin
  --                   0#
  --                 ≈≤˘⟨ 0' , -‿inverseʳ a' ⟩
  --                   a + (- a)
  --                 ≤⟨ a' +' (-' a') , ≤+-compˡ a' b' (-' a') a≤b ⟩
  --                   b + (- a)
  --                 ≤-∎⟨ b' +' (-' a') ⟩
  --         b-a≉0 = λ b-a≈0 → a≉b (
  --                             begin
  --                               a
  --                             ≈˘⟨ a' , -‿doubleInverse a' ⟩
  --                               - (- a)
  --                             ≈˘⟨ -' (-' a') , -‿uniqueˡ b' (-' a') b-a≈0 ⟩
  --                               b
  --                             ∎⟨ b' ⟩
  --                           )
  --
  -- lemma-1-3-2-⇐ : {b : A} {b' : F b} {S : A → Set}
  --              → S IsNonEmpty
  --              → b' IsUpperBoundFor S
  --              → Σ[ a ∈ A ]
  --                 Σ[ a' ∈ F a ]
  --                   (a' IsUpperBoundFor S)
  --                   × a < b
  --              → Σ[ ε ∈ A ] (F ε) × (ε > 0#)
  --                × ({x : A} → F x → S x → (x ≤ (b + (- ε))))
  -- lemma-1-3-2-⇐ {b} {b'} {S} (s , s∈S) b-isUpperBound
  --   (a , a' , a-isUpperBound , (a≤b , a≉b))
  --   = ((b + (- a)) , ((b' +' (-' a'))) , b-a>0 , ∀x∈S→x≤b-b+a)
  --   where b-a>0 = lemma-1-3-2-1 a' b' ((a≤b , a≉b))
  --         ∀x∈S→x≤b-b+a = λ {x} → λ x' → λ x∈S
  --                          → ≤-begin
  --                             x
  --                           ≤≈⟨ x' , a-isUpperBound x' x∈S ⟩
  --                             a
  --                           ≈˘⟨ a' , 0-identityˡ a' ⟩
  --                             0# + a
  --                           ≈˘⟨ 0' +' a' , +-congˡ (b' +' (-' b')) 0' a' (-‿inverseʳ b') ⟩
  --                             (b + (- b)) + a
  --                           ≈⟨ (b' +' (-' b')) +' a' , +-assoc b' (-' b') a' ⟩
  --                             b + ((- b) + a)
  --                           ≈˘⟨ b' +' ((-' b') +' a') , +-congʳ ((-' b') +' (-' (-' a'))) ((-' b') +' a') b' (+-congʳ (-' (-' a')) a' (-' b') (-‿doubleInverse a')) ⟩
  --                             b + ((- b) + (- (- a)))
  --                           ≈˘⟨ b' +' ((-' b') +' (-' (-' a'))) , +-congʳ (-' (b' +' (-' a'))) ((-' b') +' (-' (-' a'))) b' (-‿distrib b' (-' a')) ⟩
  --                             b + (- (b + (- a)))
  --                           ∎⟨ b' +' (-' (b' +' (-' a'))) ⟩
