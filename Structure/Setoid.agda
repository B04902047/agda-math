
module Structure.Setoid
        {a ℓ} {A : Set a} (_≈_ : A → A → Set ℓ) where

open import Structure.Properties
open import Structure.Subtype

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_; suc)

record IsSetoid
         (S : A → Set ℓ) : Set (a ⊔ suc ℓ) where
  field
    refl   : Reflexive _≈_ S
    sym    : Symmetric _≈_ S
    trans  : Transitive _≈_ S
    coerce : {x y : A} (P : A → Set ℓ) → S x → S y
            → x ≈ y → P x → P y
    ap     : {x y : A} (f : A → A) → S x → S y
            → x ≈ y → (f x) ≈ (f y)
  open import Structure.Reasoning.Equivalence _≈_ S refl sym trans public

record _IsSubsetoidOf_
        (T : A → Set ℓ) (S : A → Set ℓ) : Set (a ⊔ suc ℓ) where
  field
    T⊆S     : T ⊆ S
    S-isSetoid : IsSetoid S
  open IsSetoid S-isSetoid
    renaming
    ( refl   to S-refl
    ; sym    to S-sym
    ; trans  to S-trans
    ; coerce to S-coerce
    ; ap     to S-ap
    )

  T-refl : Reflexive _≈_ T
  T-refl x∈T = S-refl (T⊆S x∈T)
  T-sym : Symmetric _≈_ T
  T-sym x∈T y∈T = S-sym (T⊆S x∈T) (T⊆S y∈T)
  T-trans : Transitive _≈_ T
  T-trans x∈T y∈T z∈T = S-trans (T⊆S x∈T) (T⊆S y∈T) (T⊆S z∈T)

  T-coerce : {x y : A} (P : A → Set ℓ) → T x → T y → x ≈ y → P x → P y
  T-coerce P x∈T y∈T = S-coerce P (T⊆S x∈T) (T⊆S y∈T)
  T-ap : {x y : A} (f : A → A) → T x → T y → x ≈ y → (f x) ≈ (f y)
  T-ap f x∈T y∈T = S-ap f (T⊆S x∈T) (T⊆S y∈T)

  T-isSetoid : IsSetoid T
  T-isSetoid = record
    { refl   = T-refl
    ; sym    = T-sym
    ; trans  = T-trans
    ; coerce = T-coerce
    ; ap     = T-ap
    }

-- record Setoid : Set (a ⊔ Level.suc ℓ) where
--   field
--     carrier : A → Set ℓ
--     _≈_ : A → A → Set ℓ
--     isEquivalence : IsEquivalence _≈_ carrier

-- data _≡_ : A → A → Set (a ⊔ ℓ) where
--   refl  : {x : A} → x ≡ x
--   sym   : {x y : A} → x ≡ y → y ≡ x
--   trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
--
-- ≡-isEquivalence : (S : A → Set ℓ) → IsEquivalence _≡_ S
-- ≡-isEquivalence = ?
-- -- record
-- --   {
-- --     refl = ?
-- --   ; sym = ?
-- --   ; trans = ?
-- --   }
