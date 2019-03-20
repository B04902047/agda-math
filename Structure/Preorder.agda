------------------------------------------------------------------------
-- The basic code for preorder reasoning
-- with a predicate and a relation
------------------------------------------------------------------------

-- {-# OPTIONS --without-K --safe #-}

open import Structure.Properties using (Reflexive; Transitive)

-- only in S are reflexitivity and transitivity required
module Structure.Reasoning.Preorder
  {A : Set}
  (_≤_ : A → A → Set)
  (S : A → Set)
  (refl : Reflexive _≤_ S) (trans : Transitive _≤_ S)
  where

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

infix  4 _IsWeakerThan_
infix  3 _∎⟨_⟩
infixr 2 _≤⟨_,_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_ _≡⟨⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

record _IsWeakerThan_ (x y : A) : Set where
  field
    1∈S : S x
    2∈S : S y
    1≤2 : x ≤ y

begin_ : ∀ {x y} → x IsWeakerThan y → x ≤ y
begin relTo = _IsWeakerThan_.1≤2 relTo

_≤⟨_,_⟩_ : ∀ x {y z} → S x → x ≤ y → y IsWeakerThan z → x IsWeakerThan z
_ ≤⟨ x∈S , x≤y ⟩ relTo
  = record {
        1∈S = x∈S
      ; 2∈S = z∈S
      ; 1≤2 = (trans x∈S y∈S z∈S x≤y y≤z)
      }
    where
      y∈S = _IsWeakerThan_.1∈S relTo
      z∈S = _IsWeakerThan_.2∈S relTo
      y≤z = _IsWeakerThan_.1≤2 relTo

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsWeakerThan z → x IsWeakerThan z
_ ≡⟨ P.refl ⟩ x≤z = x≤z

_≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y IsWeakerThan z → x IsWeakerThan z
_ ≡˘⟨ P.refl ⟩ x≤z = x≤z

_≡⟨⟩_ : ∀ x {y} → x IsWeakerThan y → x IsWeakerThan y
_ ≡⟨⟩ x≤y = _ ≡⟨ P.refl ⟩ x≤y

_∎⟨_⟩ : ∀ x → S x → x IsWeakerThan x
_ ∎⟨ x∈S ⟩ = record {
              1∈S = x∈S
            ; 2∈S = x∈S
            ; 1≤2 = refl x∈S
            }

{-
private
  module Examples where
    postulate
      v w y d : A
      sw : S v
      sd : S d
      v≡w : v ≡ w
      w∼y : w ≤ y
      y≡d : y ≡ d

    u≤y : v ≤ d
    u≤y = begin
          v
        ≡⟨ v≡w ⟩
          w
        ∼⟨ sw , w≤y ⟩
          y
        ≡⟨ y≡d ⟩
          d
        ∎⟨ sd ⟩
-}
