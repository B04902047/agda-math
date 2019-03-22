
module Number.Natural where

open import Basic.Logic
open import Basic.Subtype

open import Data.Nat public
open import Data.List hiding ([_])
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst)


n≤n : (n : ℕ) → n ≤ n
n≤n zero    = z≤n
n≤n (suc n) = s≤s (n≤n n)

-- ≤-connex : (m : ℕ) → (n : ℕ)
--           → (m ≤ n) ⊎ (n ≤ m)
-- ≤-connex zero n          = inj₁ z≤n
-- ≤-connex m zero          = inj₂ z≤n
-- ≤-connex (suc m) (suc n) = [ ((λ m≤n → inj₁ (s≤s m≤n))) , (λ n≤m → inj₂ (s≤s n≤m)) ] (≤-connex m n)

≤-trans : {m n l : ℕ} → m ≤ n → n ≤ l → m ≤ l
≤-trans z≤n _ = z≤n
≤-trans (s≤s m-1≤n-1) (s≤s n-1≤l-1) = s≤s (≤-trans m-1≤n-1 n-1≤l-1)

⊔-comm : (m : ℕ) → (n : ℕ) → (m ⊔ n) ≡ (n ⊔ m)
⊔-comm zero zero = refl
⊔-comm zero (suc n) = refl
⊔-comm (suc m) zero = refl
⊔-comm (suc m) (suc n) = cong suc (⊔-comm m n)

⊔-order : (m : ℕ) → (n : ℕ)
          → (m ≤ (m ⊔ n)) × (n ≤ (m ⊔ n))
⊔-order zero n          = (z≤n , n≤n n)
⊔-order n zero          = (subst (n ≤_) (⊔-comm zero n) (n≤n n)  , z≤n)
⊔-order (suc m) (suc n) = (s≤s (proj₁ (⊔-order m n)) , s≤s (proj₂ (⊔-order m n)))

maxᴺ : ℕ → List ℕ → ℕ
maxᴺ n₀ [] = n₀
maxᴺ n₀ (n₁ ∷ ns) = n₀ ⊔ (maxᴺ n₁ ns)

ListPred : {A : Set} → (P : A → Set) → (xs : List A) → Set
ListPred {A} P [] = ⊤
ListPred {A} P (x ∷ xs) = (P x) × (ListPred P xs)

_List-⊆_ : {A : Set} (P Q : A → Set) → Set
_List-⊆_ {A} P Q = (xs : List A)
                  → (ListPred P xs) → (ListPred Q xs)

_⊆→List⊆_ : {A : Set} (P Q : A → Set)
          → P ⊆ Q → P List-⊆ Q
(P ⊆→List⊆ Q) P⊆Q [] _ = tt
(P ⊆→List⊆ Q) P⊆Q (x ∷ xs) x∷xs∈P = (P⊆Q (proj₁ x∷xs∈P) , (P ⊆→List⊆ Q) P⊆Q xs (proj₂ x∷xs∈P))

max-order : (n₀ : ℕ) → (ns : List ℕ)
            → (n₀ ≤ maxᴺ n₀ ns)
              × ListPred (_≤ maxᴺ n₀ ns) ns
max-order n₀ []        = (n≤n n₀ , tt)
max-order n₀ (n₁ ∷ ns)
  = (proj₁ (⊔-order n₀ (maxᴺ n₁ ns))
     , (≤-trans (proj₁ (max-order n₁ ns)) (proj₂ (⊔-order n₀ (maxᴺ n₁ ns)))
       , ((_≤ maxᴺ n₁ ns) ⊆→List⊆ ((_≤ n₀ ⊔ maxᴺ n₁ ns))) (λ {x} → λ x≤maxᴺ-n₁=ns → ≤-trans x≤maxᴺ-n₁=ns (proj₂ (⊔-order n₀ (maxᴺ n₁ ns)))) ns (proj₂ (max-order n₁ ns))
       )
    )
-- ListPred (_≤ n₀ ⊔ maxᴺ n₁ ns) ns
-- ListPred (_≤ maxᴺ n₁ ns) ns
