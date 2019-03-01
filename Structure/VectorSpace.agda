-- ⁰ ¹ ² ³ ⁴ ⁵ ⁶ ⁷ ⁸ ⁹ ⁺ ⁻ ⁼ ⁽ ⁾
-- ₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉ ₊ ₋ ₌ ₍ ₎
-- ᵃ ᵇ ᶜ ᵈ ᵉ ᶠ ᵍ ʰ ⁱ ʲ ᵏ ˡ ᵐ ⁿ ᵒ ᵖ ʳ ˢ ᵗ ᵘ ᵛ ʷ ˣ ʸ ᶻ
-- ᴬ ᴮ ᴰ ᴱ ᴳ ᴴ ᴵ ᴶ ᴷ ᴸ ᴹ ᴺ ᴼ ᴾ ᴿ ᵀ ᵁ ⱽ ᵂ
-- ₐ ₑ ₕ ᵢ ⱼ ₖ ₗ ₘ ₙ ₒ ₚ ᵣ ₛ ₜ ᵤ ᵥ ₓ
-- ᵅ ᵝ ᵞ ᵟ ᵋ ᶿ ᶥ ᶲ ᵠ ᵡ ᵦ ᵧ ᵨ ᵩ ᵪ'

module Structure.VectorSpace {a b ℓ₁ ℓ₂}
        {A : Set a} {B : Set b}
        (_≈ᵍ_ : A → A → Set ℓ₁) (G : A → Set ℓ₁)
        (_≈ᶠ_ : B → B → Set ℓ₂) (F : B → Set ℓ₂)
        where

open import Structure.Properties
import Structure.Group _≈ᵍ_ G as ⟨G,≈ᵍ⟩
import Structure.Field _≈ᶠ_ F as ⟨F,≈ᶠ⟩

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)


record IsVectorSpace
          (_+ᵍ_ : A → A → A) (0ᵍ : A) (-ᵍ : A → A)
          (_+ᶠ_ _*ᶠ_ : B → B → B) (0ᶠ 1ᶠ : B) (-ᶠ _⁻¹ᶠ : B → B)
          (_*ᵛ_ : B → A → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isAbelianGroup    : ⟨G,≈ᵍ⟩.IsAbelianGroup _+ᵍ_ 0ᵍ -ᵍ
    isField           : ⟨F,≈ᶠ⟩.IsField _+ᶠ_ _*ᶠ_ 0ᶠ 1ᶠ -ᶠ _⁻¹ᶠ
    _*ᵛ-close_        : {c : B} {x : A} → F c → G x → G (c *ᵛ x)
    *ᵛ-congˡ          : {c d : B} → {x : A} → c ≈ᶠ d → (c *ᵛ x) ≈ᵍ (d *ᵛ x)
    *ᵛ-congʳ          : {x y : A} {c : B} → x ≈ᵍ y → (c *ᵛ x) ≈ᵍ (c *ᵛ y)
    1ᶠ-scalarIdentity : {x : A} → G x → (1ᶠ *ᵛ x) ≈ᵍ x
    *-assoc           : {c d : B} {x : A} → F c → F d → G x
                        → ((c *ᶠ d) *ᵛ x) ≈ᵍ (c *ᵛ (d *ᵛ x))
    distribˡ          : {x : A} {c d : B} → G x → F c → F d
                        → ((c +ᶠ d) *ᵛ x) ≈ᵍ ((c *ᵛ x) +ᵍ (d *ᵛ x))
    distribʳ          : {c : B} {x y : A} → F c → G x → G y
                        → (c *ᵛ (x +ᵍ y)) ≈ᵍ ((c *ᵛ x) +ᵍ (c *ᵛ y))
