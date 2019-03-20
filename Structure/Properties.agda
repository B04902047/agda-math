
module Structure.Properties
                {A : Set}
                (_≈_ : A → A → Set)
                (S : A → Set) where

open import Level using (_⊔_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

------------------------------------------------------------------------
-- Binary Relation Properties

Reflexive : Set
Reflexive = {x : A} → S x → x ≈ x

Symmetric : Set
Symmetric = {x y : A} → S x → S y → x ≈ y → y ≈ x

Transitive : Set
Transitive = {x y z : A} → S x → S y → S z
              → x ≈ y → y ≈ z → x ≈ z

AntiSymmetric : (_≤_ : A → A → Set) → Set
AntiSymmetric _≤_ = {x y : A} → S x → S y → x ≤ y → y ≤ x → x ≈ y

Connex : Set
Connex = {x y : A} → S x → S y → (x ≈ y) ⊎ (y ≈ x)

------------------------------------------------------------------------
-- Binary Operation Properties

Congruent₂ : (_∙_ : A → A → A) → Set
Congruent₂ _∙_ = {x y u v : A} → S x → S y → S u → S v
              → x ≈ y → u ≈ v
              → (x ∙ u) ≈ (y ∙ v)

LeftCongruent : (_∙_ : A → A → A) → Set
LeftCongruent _∙_ = {x y z : A} → S x → S y → S z
                → x ≈ y
                → (x ∙ z) ≈ (y ∙ z)

getLeftCongruent : {_∙_ : A → A → A} → (refl : Reflexive) → (Congruent₂ _∙_) → (LeftCongruent _∙_)
getLeftCongruent refl ∙-cong x∈S y∈S z∈S x≈y = ∙-cong x∈S y∈S z∈S z∈S x≈y (refl z∈S)

RightCongruent : (_∙_ : A → A → A) → Set
RightCongruent _∙_ = {x y z : A} → S x → S y → S z
                → x ≈ y
                → (z ∙ x) ≈ (z ∙ y)

getRightCongruent : {_∙_ : A → A → A} → (refl : Reflexive) → (Congruent₂ _∙_) → (RightCongruent _∙_)
getRightCongruent refl ∙-cong x∈S y∈S z∈S x≈y = ∙-cong z∈S z∈S x∈S y∈S (refl z∈S) x≈y


Idempotent : (_∙_ : A → A → A) → Set
Idempotent _∙_ = {x : A} → (x ∙ x) ≈ x

Closed₂ : (_∙_ : A → A → A) → Set
Closed₂ _∙_ = {x y : A} → S x → S y → S (x ∙ y)

Associative : (_∙_ : A → A → A) → Set
Associative _∙_ = {x y z : A} → S x → S y → S z
                 → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : (_∙_ : A → A → A) → Set
Commutative _∙_ = {x y : A} → S x → S y
                  → (x ∙ y) ≈ (y ∙ x)

------------------------------------------------------------------------
-- Identity Properties

Closed₀ : (ε : A) → Set
Closed₀ ε = S ε

LeftIdentity : (_∙_ : A → A → A) → (ε : A) → Set
LeftIdentity _∙_ ε = {x : A} → S x → (ε ∙ x) ≈ x

RightIdentity : (_∙_ : A → A → A) → (ε : A) → Set
RightIdentity _∙_ ε = {x : A} → S x → (x ∙ ε) ≈ x

Identity : (_∙_ : A → A → A) → (ε : A) → Set
Identity _∙_ ε = (LeftIdentity _∙_ ε) × (RightIdentity _∙_ ε)

LeftZero : (_∙_ : A → A → A) → (ε : A) → Set
LeftZero _∙_ z = {x : A} → S x → (z ∙ x) ≈ z

RightZero : (_∙_ : A → A → A) → (ε : A) → Set
RightZero _∙_ z = {x : A} → S x → (x ∙ z) ≈ z

Zero : (_∙_ : A → A → A) → (ε : A) → Set
Zero z ∙ = LeftZero z ∙ × RightZero z ∙

------------------------------------------------------------------------
-- Inverse Properties

LeftInverse : (_∙_ : A → A → A) → (ε : A) → (_⁻¹ : A → A) → Set
LeftInverse _∙_ ε _⁻¹ = {x : A} → S x
                        → ((x ⁻¹) ∙ x) ≈ ε

RightInverse : (_∙_ : A → A → A) → (ε : A) → (_⁻¹ : A → A) → Set
RightInverse _∙_ ε _⁻¹ = {x : A} → S x
                        → (x ∙ (x ⁻¹)) ≈ ε

Inverse : (_∙_ : A → A → A) → (ε : A) → (_⁻¹ : A → A) → Set
Inverse _∙_ ε _⁻¹ = {x : A} → S x
                    → ((((x ⁻¹) ∙ x) ≈ ε) × ((x ∙ (x ⁻¹)) ≈ ε))

Congruent₁ : (f : A → A) → Set
Congruent₁ f = {x y : A} → S x → S y → x ≈ y → (f x) ≈ (f y)

Closed₁ : (f : A → A) → Set
Closed₁ f = {x : A} → S x → S (f x)

------------------------------------------------------------------------
-- 2 Binary Operations Properties

_DistributesOverˡ_ : (_*_ _+_ : A → A → A) → Set
_*_ DistributesOverˡ _+_ = {x y z : A} → S x → S y → S z
                          → (x * (y + z)) ≈ ((x * y) + (x * z))

_DistributesOverʳ_ : (_*_ _+_ : A → A → A) → Set
_*_ DistributesOverʳ _+_ = {x y z : A} → S x → S y → S z
                          → ((y + z) * x) ≈ ((y * x) + (z * x))

_DistributesOver_ : (* + : A → A → A) → Set
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)
