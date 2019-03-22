
module Basic.Equality {A : Set} where

open import Basic.Properties
open import Basic.Setoid

open import Relation.Binary.PropositionalEquality
            renaming
              ( _≡_ to _≡'_
              ; refl to refl'
              ; sym  to sym'
              ; trans to trans'
              ; subst to subst'
              ; cong to cong'
              )


_≡_ : A → A → Set
_≡_ = _≡'_

refl : (S : A → Set) → Reflexive _≡_ S
refl S _ = refl'

trans : (S : A → Set) → Transitive _≡_ S
trans S _ _ _ = trans'

sym : (S : A → Set) → Symmetric _≡_ S
sym S _ _ = sym'

coerce : (S : A → Set) → {x y : A} (P : A → Set) → S x → S y
        → x ≡ y → P x → P y
coerce S P _ _ = subst' P

ap : (S : A → Set) → {x y : A} (f : A → A) → S x → S y
      → x ≡ y → (f x) ≡ (f y)
ap S f _ _ = cong' f

≡-isSet : (S : A → Set) → IsSet _≡_ S
≡-isSet S = record
  { refl   = refl S
  ; sym    = sym S
  ; trans  = trans S
  ; coerce = coerce S
  ; ap     = ap S
  }
