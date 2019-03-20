
module Structure.Setoid {A : Set} (_≈_ : A → A → Set) where

open import Structure.Properties
open import Structure.Subtype
open import Structure.Logic

record IsSet (S : A → Set) : Set₁ where
  field
    refl   : Reflexive _≈_ S
    sym    : Symmetric _≈_ S
    trans  : Transitive _≈_ S
    coerce : {x y : A} (P : A → Set) → S x → S y
            → x ≈ y → P x → P y
    ap     : {x y : A} (f : A → A) → S x → S y
            → x ≈ y → (f x) ≈ (f y)
  open import Structure.Reasoning.Equivalence _≈_ S refl sym trans public

record _IsSubsetOf_ (T S : A → Set) : Set₁ where
  field
    T⊆S     : T ⊆ S
    S-isSet : IsSet S
  open IsSet S-isSet
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

  T-coerce : {x y : A} (P : A → Set) → T x → T y → x ≈ y → P x → P y
  T-coerce P x∈T y∈T = S-coerce P (T⊆S x∈T) (T⊆S y∈T)
  T-ap : {x y : A} (f : A → A) → T x → T y → x ≈ y → (f x) ≈ (f y)
  T-ap f x∈T y∈T = S-ap f (T⊆S x∈T) (T⊆S y∈T)

  T-isSet : IsSet T
  T-isSet = record
    { refl   = T-refl
    ; sym    = T-sym
    ; trans  = T-trans
    ; coerce = T-coerce
    ; ap     = T-ap
    }
