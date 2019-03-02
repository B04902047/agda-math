
module Structure.Equivalence {a ℓ} {A : Set a} where

open import Structure.Properties

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

record IsEquivalence
        (_≈_ : A → A → Set ℓ) (S : A → Set ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive _≈_ S
    sym   : Symmetric _≈_ S
    trans : Transitive _≈_ S
  open import Structure.Reasoning.Equivalence _≈_ S refl sym trans public

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
