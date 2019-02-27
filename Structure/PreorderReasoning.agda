------------------------------------------------------------------------
-- The basic code for equational reasoning
-- with a predicate and a relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Properties using (Reflexive; Transitive)

-- only in S are reflexitivity and transitivity required
module PreorderReasoning
  {a ℓ} {A : Set a}
  (_∼_ : A → A → Set ℓ) (S : A → Set ℓ)
  (refl : Reflexive _∼_ S) (trans : Transitive _∼_ S)
  where

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

infix  4 _IsRelatedTo_
infix  3 _∎⟨_⟩
infixr 2 _∼⟨_,_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_ _≡⟨⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

record _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ) where
  field
    s1  : S x
    s2  : S y
    1∼2 : x ∼ y

begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
begin relTo = _IsRelatedTo_.1∼2 relTo

_∼⟨_,_⟩_ : ∀ x {y z} → S x → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ sx , x∼y ⟩ relTo =
          record {
            s1 = sx
          ; s2 = sz
          ; 1∼2 = (trans sx sy sz x∼y y∼z)
          }
          where
            sy = _IsRelatedTo_.s1 relTo
            sz = _IsRelatedTo_.s2 relTo
            y∼z = _IsRelatedTo_.1∼2 relTo

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_ ≡⟨ P.refl ⟩ x∼z = x∼z

_≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
_ ≡˘⟨ P.refl ⟩ x∼z = x∼z

_≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≡⟨⟩ x∼y = _ ≡⟨ P.refl ⟩ x∼y

_∎⟨_⟩ : ∀ x → S x → x IsRelatedTo x
_ ∎⟨ sx ⟩ = record {
              s1 = sx
            ; s2 = sx
            ; 1∼2 = refl sx
            }

{-
private
  module Examples where
    postulate
      v w y d : A
      sw : S v
      sd : S d
      v≡w : v ≡ w
      w∼y : w ∼ y
      y≡d : y ≡ d

    u∼y : v ∼ d
    u∼y = begin
          v
        ≡⟨ v≡w ⟩
          w
        ∼⟨ sw , w∼y ⟩
          y
        ≡⟨ y≡d ⟩
          d
        ∎⟨ sd ⟩
-}
