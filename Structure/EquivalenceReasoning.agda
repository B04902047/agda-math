
open import Properties using (Reflexive; Symmetric; Transitive)

module EquivalenceReasoning
  {a ℓ} {A : Set a}
  (_∼_ : A → A → Set ℓ) (S : A → Set ℓ)
  (refl : Reflexive _∼_ S)
  (sym : Symmetric _∼_ S)
  (trans : Transitive _∼_ S)
  where

open import PreorderReasoning _∼_ S refl trans public

infixr 2 _∼˘⟨_,_⟩_

_∼˘⟨_,_⟩_ : ∀ x {y z} → S x → y ∼ x → y IsRelatedTo z → x IsRelatedTo z
_ ∼˘⟨ sx , y∼x ⟩ relTo =
        record {
          s1 = sx
        ; s2 = sz
        ; 1∼2 = (trans sx sy sz (sym sy sx y∼x) y∼z)
        }
        where
          sy = _IsRelatedTo_.s1 relTo
          sz = _IsRelatedTo_.s2 relTo
          y∼z = _IsRelatedTo_.1∼2 relTo
