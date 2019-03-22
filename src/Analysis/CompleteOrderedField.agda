
module Analysis.CompleteOrderedField {A : Set} (_≈_ : A → A → Set) where

open import Analysis.OrderedField _≈_
open import Basic.Logic
open import Basic.Properties _≈_
open import Basic.Subtype

record IsCompleteOrderedField
        (ℝ : A → Set)
        (_+_ _*_ : A → A → A)
        (0# 1# : A) (- _⁻¹ : A → A)
        (_≤_ : A → A → Set) : Set₁ where
  field
    isOrderedField : IsOrderedField ℝ _+_ _*_ 0# 1# - _⁻¹ _≤_
    completeness   : IsOrderedField.MonotoneSequeceProperty isOrderedField

  cauchyCompleteness   : IsOrderedField.CauchyComplete isOrderedField


  open IsOrderedField isOrderedField public

record IsCompleteOrderedField'
        (ℝ : A → Set)
        (_+_ _*_ : A → A → A)
        (0# 1# : A) (- _⁻¹ : A → A)
        (_≤_ : A → A → Set) : Set₁ where
  field
    isOrderedField : IsOrderedField ℝ _+_ _*_ 0# 1# - _⁻¹ _≤_
    cauchyCompleteness   : IsOrderedField.CauchyComplete isOrderedField

  open IsOrderedField isOrderedField public
