
module Basic.Morphism where

open import Basic.Setoid
open import Basic.Logic

open import Data.Nat

_-aryOperation_ : ℕ → Set → Set
zero    -aryOperation A = A
(suc n) -aryOperation A = A → (n -aryOperation A)

_-aryRelation_ : ℕ → Set → Set₁
zero    -aryRelation A = Set
(suc n) -aryRelation A = A → (n -aryRelation A)

record IsFunction {A B : Set} (φ : A → B)
                  (_≈₁_ : A → A → Set) (S : A → Set)
                  (_≈₂_ : B → B → Set) (T : B → Set) : Set₁ where
  field
    S-isSet : IsSet _≈₁_ S
    T-isSet : IsSet _≈₂_ T
    φ-close : {x : A} → S x → T (φ x)

  Injective : Set
  Injective = {x y : A} → S x → S y
            → ¬ (x ≈₁ y) → ¬ ((φ x) ≈₂ (φ y))

  Surjective : Set
  Surjective = {y : B} → T y
             → Σ[ x ∈ A ] ((S x) × ((φ x) ≈₂ y))

  Bijective : Set
  Bijective = Injective × Surjective

  isHomomorphism-R : {n : ℕ} (R : n -aryRelation A)
                   → (R' : n -aryRelation B) → Set
  isHomomorphism-R {zero} R R' = R → R'
  isHomomorphism-R {suc n} R R'
    = {x : A} → isHomomorphism-R {n} (R x) (R' (φ x))

  isHomomorphism-c : (c : A) → (c' : B) → Set
  isHomomorphism-c c c' = φ c ≈₂ c'

  isHomomorphism-f : {n : ℕ} (f : n -aryOperation A)
                   → (f' : n -aryOperation B) → Set
  isHomomorphism-f {zero} = isHomomorphism-c
  isHomomorphism-f {suc n} f f'
    = {x : A} → isHomomorphism-f {n} (f x) (f' (φ x))

  φ-close' : isHomomorphism-R S T
  φ-close' = φ-close

  image : ({x : A} → S x → Set)
        → {y : B} → T y → Set
  image R {y} y' = Σ[ x ∈ A ] Σ[ x' ∈ S x ] (R x') × (φ x ≈₂ y)

  preImage : ({y : B} → T y → Set)
           → {x : A} → S x → Set
  preImage R' x' = R' (φ-close x')

  S' : {x : A} → S x → Set
  S' {x} _ = S x

  T' : {y : B} → T y → Set
  T' {y} _ = T y

  φ-close'' : {y : B} {y' : T y}
            → image S' y' → T' y'
  φ-close'' {y} {y'} _ = y'
  -- -- isHomo-id : isHomomorphism-f id id --φ-close x∈S
  -- isHomo-id {x} = IsSet.refl T-isSet (φ-close {!   !})

IsOperation : {A : Set} (φ : A → A)
            → (_≈_ : A → A → Set)
            → (S : A → Set)
            → Set₁
IsOperation φ _≈_ S = IsFunction φ _≈_ S _≈_ S
