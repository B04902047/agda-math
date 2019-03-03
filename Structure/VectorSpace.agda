-- ⁰ ¹ ² ³ ⁴ ⁵ ⁶ ⁷ ⁸ ⁹ ⁺ ⁻ ⁼ ⁽ ⁾
-- ₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉ ₊ ₋ ₌ ₍ ₎
-- ᵃ ᵇ ᶜ ᵈ ᵉ ᶠ ᵍ ʰ ⁱ ʲ ᵏ ˡ ᵐ ⁿ ᵒ ᵖ ʳ ˢ ᵗ ᵘ ᵛ ʷ ˣ ʸ ᶻ
-- ᴬ ᴮ ᴰ ᴱ ᴳ ᴴ ᴵ ᴶ ᴷ ᴸ ᴹ ᴺ ᴼ ᴾ ᴿ ᵀ ᵁ ⱽ ᵂ
-- ₐ ₑ ₕ ᵢ ⱼ ₖ ₗ ₘ ₙ ₒ ₚ ᵣ ₛ ₜ ᵤ ᵥ ₓ
-- ᵅ ᵝ ᵞ ᵟ ᵋ ᶿ ᶥ ᶲ ᵠ ᵡ ᵦ ᵧ ᵨ ᵩ ᵪ'

module Structure.VectorSpace {a b ℓ₁ ℓ₂}
        {A : Set a} {B : Set b}
        (_≈ᵍ_ : A → A → Set ℓ₁)
        (_≈ᶠ_ : B → B → Set ℓ₂)
        where

open import Structure.Properties
import Structure.Group _≈ᵍ_ as ⟨A,≈ᵍ⟩
import Structure.Field _≈ᶠ_ as ⟨B,≈ᶠ⟩
open import Structure.Subtype

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_; suc)


record IsVectorSpace
        (G : A → Set ℓ₁)
        (_+ᵍ_ : A → A → A) (0ᵍ : A) (-ᵍ : A → A)
        (F : B → Set ℓ₂)
        (_+ᶠ_ _*ᶠ_ : B → B → B) (0ᶠ 1ᶠ : B) (-ᶠ _⁻¹ᶠ : B → B)
        (_*ᵛ_ : B → A → A)
                                : Set (a ⊔ b ⊔ suc ℓ₁ ⊔ suc ℓ₂) where
  field
    G-isAbelianGroup  : ⟨A,≈ᵍ⟩.IsAbelianGroup G _+ᵍ_ 0ᵍ -ᵍ
    F-isField         : ⟨B,≈ᶠ⟩.IsField F _+ᶠ_ _*ᶠ_ 0ᶠ 1ᶠ -ᶠ _⁻¹ᶠ
    _*ᵛ-close_        : {c : B} {x : A} → F c → G x → G (c *ᵛ x)
    *ᵛ-congˡ          : {c d : B} {x : A} → F c → F d → G x
                        → c ≈ᶠ d → (c *ᵛ x) ≈ᵍ (d *ᵛ x)
    *ᵛ-congʳ          : {x y : A} {c : B} → G x → G y → F c
                        → x ≈ᵍ y → (c *ᵛ x) ≈ᵍ (c *ᵛ y)
    1ᶠ-scalarIdentity : {x : A} → G x → (1ᶠ *ᵛ x) ≈ᵍ x
    *-assoc           : {c d : B} {x : A} → F c → F d → G x
                        → ((c *ᶠ d) *ᵛ x) ≈ᵍ (c *ᵛ (d *ᵛ x))
    distribʳ          : {x : A} {c d : B} → G x → F c → F d
                        → ((c +ᶠ d) *ᵛ x) ≈ᵍ ((c *ᵛ x) +ᵍ (d *ᵛ x))
    distribˡ          : {c : B} {x y : A} → F c → G x → G y
                        → (c *ᵛ (x +ᵍ y)) ≈ᵍ ((c *ᵛ x) +ᵍ (c *ᵛ y))

  open ⟨A,≈ᵍ⟩.IsAbelianGroup G-isAbelianGroup public
    renaming
    ( ∙-comm              to +ᵍ-comm
    ; isGroup             to +ᵍ-isGroup
    ;   _⁻¹-close         to -ᵍ‿close
    ;   _⁻¹-inverse       to -ᵍ‿inverse
    ;     _⁻¹-inverseˡ    to -ᵍ‿inverseˡ
    ;     _⁻¹-inverseʳ    to -ᵍ‿inverseʳ
    ;   ⁻¹-cong           to -ᵍ‿cong
    ;     ⁻¹-uniqueˡ      to -ᵍ‿uniqueˡ
    ;     ⁻¹-uniqueʳ      to -ᵍ‿uniqueʳ
    ;     ∙-cancelˡ       to +ᵍ-cancelˡ
    ;     ∙-cancelʳ       to +ᵍ-cancelʳ
    ;     _/_             to _-ᵍ_
    ;     _/-close_       to _-ᵍ‿close_
    ;     /-congˡ         to -ᵍ‿congˡ
    ;     /-congʳ         to -ᵍ‿congʳ
    ;   isMonoid          to +ᵍ-isMonoid
    ;     ε-close         to 0ᵍ-close
    ;     ε-identity      to 0ᵍ-identity
    ;       ε-identityˡ   to 0ᵍ-identityˡ
    ;       _ε-identityʳ  to _0ᵍ-identityʳ
    ;       ε-uniqueˡ     to 0ᵍ-uniqueˡ
    ;       ε-uniqueʳ     to 0ᵍ-uniqueʳ
    ;     isSemigroup     to +ᵍ-isSemigroup
    ;       ∙-assoc       to +ᵍ-assoc
    ;       isMagma       to +ᵍ-isMagma
    ;         _∙-close_   to _+ᵍ-close_
    ;         ∙-congˡ     to +ᵍ-congˡ
    ;         ∙-congʳ     to +ᵍ-congʳ
    ;         isSetoid    to G-isSetoid
    ;           refl      to G-refl
    ;           sym       to G-sym
    ;           trans     to G-trans
    ;           coerce    to G-coerce
    ;           ap        to G-ap
    ; isCommutativeMonoid to +ᵍ-isCommutativeMonoid
    )
  open ⟨B,≈ᶠ⟩.IsField F-isField public
    renaming
    ( isDivisionRing to F-isDivisionRing
    ;   isRing       to F-isRing
    ;     +-isAbelianGroup  to +ᶠ-isAbelianGroup
    ;       +-comm              to +ᶠ-comm
    ;       +-isGroup             to +ᶠ-isGroup
    ;         -‿close         to -ᶠ‿close
    ;         -‿inverse       to -ᶠ‿inverse
    ;          -‿inverseˡ    to -ᶠ‿inverseˡ
    ;           -‿inverseʳ    to -ᶠ‿inverseʳ
    ;         -‿cong           to -ᶠ‿cong
    ;           -‿uniqueˡ      to -ᶠ‿uniqueˡ
    ;           -‿uniqueʳ      to -ᶠ‿uniqueʳ
    ;           +-cancelˡ       to +ᶠ-cancelˡ
    ;           +-cancelʳ       to +ᶠ-cancelʳ
    ;           _-_             to _-ᶠ_
    ;           _-‿close_       to _-ᶠ‿close_
    ;           -‿congˡ         to -ᶠ‿congˡ
    ;           -‿congʳ         to -ᶠ‿congʳ
    ;         +-isMonoid        to +ᶠ-isMonoid
    ;           0-close         to 0ᶠ-close
    ;           0-identity      to 0ᶠ-identity
    ;             0-identityˡ   to 0ᶠ-identityˡ
    ;             _0-identityʳ  to _0ᶠ-identityʳ
    ;             0-uniqueˡ     to 0ᶠ-uniqueˡ
    ;             0-uniqueʳ     to 0ᶠ-uniqueʳ
    ;           +-isSemigroup   to +ᶠ-isSemigroup
    ;             +-assoc       to +ᶠ-assoc
    ;             +-isMagma     to +ᶠ-isMagma
    ;               _+-close_   to _+ᶠ-close_
    ;               +-congˡ     to +ᶠ-congˡ
    ;               +-congʳ     to +ᶠ-congʳ
    ;       +-isCommutativeMonoid to +ᶠ-isCommutativeMonoid
    ;       _⁻¹-close\[0]   to _⁻¹ᶠ-close\[0]
    ;       ⁻¹-cong\[0]     to ⁻¹ᶠ-cong\[0]
    ;       _⁻¹-inverse\[0] to _⁻¹ᶠ-inverse\[0]
    ;         _⁻¹-inverse\[0]ˡ to _⁻¹ᶠ-inverse\[0]ˡ
    ;         _⁻¹-inverse\[0]ʳ to _⁻¹ᶠ-inverse\[0]ʳ
    ;         *-cancel\[0]ˡ to *ᶠ-cancel\[0]ˡ
    ;         *-cancel\[0]ʳ to *ᶠ-cancel\[0]ʳ
    ;       _/_           to _/ᶠ_
    ;       _/-close\[0]_ to _/ᶠ-close\[0]_
    ;       /-cong\[0]ˡ   to /ᶠ-cong\[0]ˡ
    ;       /-cong\[0]ʳ   to /ᶠ-cong\[0]ʳ
    ;     *-isMonoid      to *ᶠ-isMonoid
    ;       1-close         to 1ᶠ-close
    ;       1-identity      to 1ᶠ-identity
    ;         1-identityˡ   to 1ᶠ-identityˡ
    ;         _1-identityʳ  to _1ᶠ-identityʳ
    ;         1-uniqueˡ     to 1ᶠ-uniqueˡ
    ;         1-uniqueʳ     to 1ᶠ-uniqueʳ
    ;       *-isSemigroup     to *ᶠ-isSemigroup
    ;         *-assoc       to *ᶠ-assoc
    ;         *-isMagma       to *ᶠ-isMagma
    ;           _*-close_   to _*ᶠ-close_
    ;           *-congˡ     to *ᶠ-congˡ
    ;           *-congʳ     to *ᶠ-congʳ
    ;           isSetoid    to F-isSetoid
    ;             refl      to F-refl
    ;             sym       to F-sym
    ;             trans     to F-trans
    ;             coerce    to F-coerce
    ;             ap        to F-ap
    ;     distrib         to F-distrib
    ;     distribˡ        to F-distribˡ
    ;     distribʳ        to F-distribʳ
    ;   0-zeroˡ           to 0ᶠ-zeroˡ
    ;   _0-zeroʳ          to _0ᶠ-zeroʳ
    ;   negativeUnit      to F-negativeUnit
    ; *-comm              to *ᶠ-comm
    ; 1!≈0                 to 1ᶠ!≈ᶠ0ᶠ
    ;   noNonzeroZeroDivisors to F-noNonzeroZeroDivisors
    ;   isIntegralDomain      to F-isIntegralDomain
    ;   isSetoid\[0]          to F\[0]-isSetoid
    ;   _*-close\[0]_         to _*ᶠ-close\[0]_
    ;   *-congˡ\[0]           to *ᶠ-congˡ\[0]
    ;   *-congʳ\[0]           to *ᶠ-congʳ\[0]
    ;   *-isMagma\[0]         to *ᶠ-isMagma\[0]
    ;   *-assoc\[0]           to *ᶠ-assoc\[0]
    ;   *-isSemigroup\[0]     to *-isSemigroup\[0]
    ;   1-identityˡ\[0]       to 1ᶠ-identityˡ\[0]
    ;   _1-identityʳ\[0]      to _1ᶠ-identityʳ\[0]
    ;   *-isMonoid\[0]       to *ᶠ-isMonoid\[0]
    ;   *-isGroup\[0]        to *ᶠ-isGroup\[0]
    ;   *-comm\[0]           to *ᶠ-comm\[0]
    ;   *-isAbelianGroup\[0] to *ᶠ-isAbelianGroup\[0]
    )
    hiding
    ( _IsEquivalentTo_
    ; begin_
    ; _≈⟨_,_⟩_
    ; _≈˘⟨_,_⟩_
    ; _≡⟨_⟩_
    ; _≡˘⟨_⟩_
    ; _≡⟨⟩_; _∎⟨_⟩
    )

  0ᶠ-scalarZero : {x : A} → G x → (0ᶠ *ᵛ x) ≈ᵍ 0ᵍ
  0ᶠ-scalarZero {x} x∈G
    = +ᵍ-cancelˡ (0ᶠ-close *ᵛ-close x∈G) 0ᵍ-close (0ᶠ-close *ᵛ-close x∈G) 0*x+0*x=0*x
    where 0*x+0*x=0*x = begin
                        (0ᶠ *ᵛ x) +ᵍ (0ᶠ *ᵛ x)
                      ≈˘⟨ (0ᶠ-close *ᵛ-close x∈G) +ᵍ-close (0ᶠ-close *ᵛ-close x∈G) , distribʳ x∈G 0ᶠ-close 0ᶠ-close ⟩
                        (0ᶠ +ᶠ 0ᶠ) *ᵛ x
                      ≈⟨ (0ᶠ-close +ᶠ-close 0ᶠ-close) *ᵛ-close x∈G , *ᵛ-congˡ (0ᶠ-close +ᶠ-close 0ᶠ-close) 0ᶠ-close x∈G (0ᶠ-close 0ᶠ-identityʳ) ⟩
                        0ᶠ *ᵛ x
                      ≈˘⟨ 0ᶠ-close *ᵛ-close x∈G , (0ᶠ-close *ᵛ-close x∈G) 0ᵍ-identityʳ ⟩
                        (0ᶠ *ᵛ x) +ᵍ 0ᵍ
                      ∎⟨ (0ᶠ-close *ᵛ-close x∈G) +ᵍ-close 0ᵍ-close ⟩

  Theorem-1-2 : {x : A} → G x → ((-ᶠ 1ᶠ) *ᵛ x) ≈ᵍ (-ᵍ x)
  Theorem-1-2 {x} x∈G = -ᵍ‿uniqueˡ ((-ᶠ‿close 1ᶠ-close) *ᵛ-close x∈G) x∈G -1*x+x≈0
                        where -1*x+x≈0 = begin
                                          ((-ᶠ 1ᶠ) *ᵛ x) +ᵍ x
                                        ≈˘⟨ ((-ᶠ‿close 1ᶠ-close) *ᵛ-close x∈G) +ᵍ-close x∈G , +ᵍ-congʳ ((1ᶠ-close *ᵛ-close x∈G)) x∈G ((-ᶠ‿close 1ᶠ-close) *ᵛ-close x∈G) (1ᶠ-scalarIdentity x∈G) ⟩
                                          ((-ᶠ 1ᶠ) *ᵛ x) +ᵍ (1ᶠ *ᵛ x)
                                        ≈˘⟨ ((-ᶠ‿close 1ᶠ-close) *ᵛ-close x∈G) +ᵍ-close (1ᶠ-close *ᵛ-close x∈G) , distribʳ x∈G (-ᶠ‿close 1ᶠ-close) 1ᶠ-close ⟩
                                          ((-ᶠ 1ᶠ) +ᶠ 1ᶠ) *ᵛ x
                                        ≈⟨ ((-ᶠ‿close 1ᶠ-close) +ᶠ-close 1ᶠ-close) *ᵛ-close x∈G , *ᵛ-congˡ ((-ᶠ‿close 1ᶠ-close) +ᶠ-close 1ᶠ-close) 0ᶠ-close x∈G (-ᶠ‿inverseˡ 1ᶠ-close) ⟩
                                          0ᶠ *ᵛ x
                                        ≈⟨ 0ᶠ-close *ᵛ-close x∈G , 0ᶠ-scalarZero x∈G ⟩
                                          0ᵍ
                                        ∎⟨ 0ᵍ-close ⟩


record _IsSubspaceOf_
        (H : A → Set ℓ₁)
        (G : A → Set ℓ₁)
        (_+ᵍ_ : A → A → A) (0ᵍ : A) (-ᵍ : A → A)
        (F : B → Set ℓ₂)
        (_+ᶠ_ _*ᶠ_ : B → B → B) (0ᶠ 1ᶠ : B) (-ᶠ _⁻¹ᶠ : B → B)
        (_*ᵛ_ : B → A → A)
                        : Set (a ⊔ b ⊔ suc ℓ₁ ⊔ suc ℓ₂) where
  field
    H⊆G             : H ⊆ G
    G-isVectorSpace : IsVectorSpace G _+ᵍ_ 0ᵍ -ᵍ F _+ᶠ_ _*ᶠ_ 0ᶠ 1ᶠ -ᶠ _⁻¹ᶠ _*ᵛ_
    H-isVectorSpace : IsVectorSpace H _+ᵍ_ 0ᵍ -ᵍ F _+ᶠ_ _*ᶠ_ 0ᶠ 1ᶠ -ᶠ _⁻¹ᶠ _*ᵛ_

record _IsSubspaceOf'_
        (H : A → Set ℓ₁)
        (G : A → Set ℓ₁)
        (_+ᵍ_ : A → A → A) (0ᵍ : A) (-ᵍ : A → A)
        (F : B → Set ℓ₂)
        (_+ᶠ_ _*ᶠ_ : B → B → B) (0ᶠ 1ᶠ : B) (-ᶠ _⁻¹ᶠ : B → B)
        (_*ᵛ_ : B → A → A)
                        : Set (a ⊔ b ⊔ suc ℓ₁ ⊔ suc ℓ₂) where
  field
    H⊆G             : H ⊆ G
    G-isVectorSpace : IsVectorSpace G _+ᵍ_ 0ᵍ -ᵍ F _+ᶠ_ _*ᶠ_ 0ᶠ 1ᶠ -ᶠ _⁻¹ᶠ _*ᵛ_
    _*ᵛ-close-H_    : {c : B} {x : A} → F c → H x → H (c *ᵛ x)
    _+ᵍ-close-H_    : Closed₂ _≈ᵍ_ H _+ᵍ_
    0ᵍ-close-H      : H 0ᵍ

  open IsVectorSpace G-isVectorSpace

  -ᵍ‿close-H : Closed₁ _≈ᵍ_ H -ᵍ
  -ᵍ‿close-H x∈H = G-coerce H ((-ᶠ‿close 1ᶠ-close) *ᵛ-close (H⊆G x∈H)) (-ᵍ‿close (H⊆G x∈H)) (Theorem-1-2 (H⊆G x∈H)) ((-ᶠ‿close 1ᶠ-close) *ᵛ-close-H x∈H)

  H-isSubgroupOf'-G : (H ⟨A,≈ᵍ⟩.IsSubgroupOf' G) _+ᵍ_ 0ᵍ -ᵍ
  H-isSubgroupOf'-G = record
   { H⊆G         = H⊆G
   ; G-isGroup   = +ᵍ-isGroup
   ; _∙-close-H_ = _+ᵍ-close-H_
   ; ε-close-H   = 0ᵍ-close-H
   ; _⁻¹-close-H = -ᵍ‿close-H
   }

  H-isGroup : ⟨A,≈ᵍ⟩.IsGroup H _+ᵍ_ 0ᵍ -ᵍ
  H-isGroup = ⟨A,≈ᵍ⟩._IsSubgroupOf'_.H-isGroup H-isSubgroupOf'-G

  +ᵍ-comm-H : {x y : A} → H x → H y → (x +ᵍ y) ≈ᵍ (y +ᵍ x)
  +ᵍ-comm-H x∈H y∈H = +ᵍ-comm (H⊆G x∈H) (H⊆G y∈H)

  H-isAbelianGroup : ⟨A,≈ᵍ⟩.IsAbelianGroup H _+ᵍ_ 0ᵍ -ᵍ
  H-isAbelianGroup = record
    { isGroup = H-isGroup
    ; ∙-comm  = +ᵍ-comm-H
    }

  *ᵛ-congˡ-H : {c d : B} {x : A} → F c → F d → H x
              → c ≈ᶠ d → (c *ᵛ x) ≈ᵍ (d *ᵛ x)
  *ᵛ-congˡ-H c∈F d∈F x∈H c≈ᶠd = *ᵛ-congˡ c∈F d∈F (H⊆G x∈H) c≈ᶠd

  *ᵛ-congʳ-H : {x y : A} {c : B} → H x → H y → F c
              → x ≈ᵍ y → (c *ᵛ x) ≈ᵍ (c *ᵛ y)
  *ᵛ-congʳ-H x∈H y∈H c∈F x≈ᵍy = *ᵛ-congʳ x∈G y∈G c∈F x≈ᵍy
                                where x∈G = H⊆G x∈H
                                      y∈G = H⊆G y∈H

  1ᶠ-scalarIdentity-H : {x : A} → H x → (1ᶠ *ᵛ x) ≈ᵍ x
  1ᶠ-scalarIdentity-H x∈H = 1ᶠ-scalarIdentity x∈G
                            where x∈G = H⊆G x∈H

  *-assoc-H : {c d : B} {x : A} → F c → F d → H x
              → ((c *ᶠ d) *ᵛ x) ≈ᵍ (c *ᵛ (d *ᵛ x))
  *-assoc-H c∈F d∈F x∈H = *-assoc c∈F d∈F x∈G
                          where x∈G = H⊆G x∈H

  H-distribʳ : {x : A} {c d : B} → H x → F c → F d
              → ((c +ᶠ d) *ᵛ x) ≈ᵍ ((c *ᵛ x) +ᵍ (d *ᵛ x))
  H-distribʳ x∈H = distribʳ x∈G where x∈G = H⊆G x∈H

  H-distribˡ : {c : B} {x y : A} →
        F c → H x → H y → (c *ᵛ (x +ᵍ y)) ≈ᵍ ((c *ᵛ x) +ᵍ (c *ᵛ y))
  H-distribˡ c∈F x∈H y∈H = distribˡ c∈F x∈G y∈G where x∈G = H⊆G x∈H
                                                      y∈G = H⊆G y∈H

  H-isVectorSpace : ((IsVectorSpace H _+ᵍ_ 0ᵍ -ᵍ) F _+ᶠ_ _*ᶠ_ 0ᶠ 1ᶠ -ᶠ) _⁻¹ᶠ _*ᵛ_
  H-isVectorSpace = record
    { G-isAbelianGroup  = H-isAbelianGroup
    ; F-isField         = F-isField
    ; _*ᵛ-close_        = _*ᵛ-close-H_
    ; *ᵛ-congˡ          = *ᵛ-congˡ-H
    ; *ᵛ-congʳ          = *ᵛ-congʳ-H
    ; 1ᶠ-scalarIdentity = 1ᶠ-scalarIdentity-H
    ; *-assoc           = *-assoc-H
    ; distribˡ          = H-distribˡ
    ; distribʳ          = H-distribʳ
    }

  Theorem-1-3 : (((H IsSubspaceOf G) _+ᵍ_ 0ᵍ -ᵍ) F _+ᶠ_ _*ᶠ_ 0ᶠ 1ᶠ -ᶠ) _⁻¹ᶠ _*ᵛ_
  Theorem-1-3 = record
    { H⊆G             = H⊆G
    ; G-isVectorSpace = G-isVectorSpace
    ; H-isVectorSpace = H-isVectorSpace
    }
