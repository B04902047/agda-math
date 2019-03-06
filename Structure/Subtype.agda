
module Structure.Subtype {a ℓ} {A : Set a} where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

_\[_] : (P : A → Set ℓ) → (Q : A → Set ℓ) → A → Set ℓ
P \[ Q ] = λ x → ((P x) × (¬ (Q x)))

data ⊤ : Set ℓ where
  true : ⊤

_⊆_ : (P : A → Set ℓ) → (Q : A → Set ℓ) → Set (a ⊔ ℓ)
P ⊆ Q = {x : A} → P x → Q x

_∪_ : (P : A → Set ℓ) → (Q : A → Set ℓ) → A → Set ℓ
(P ∪ Q) x = (P x) ⊎ (Q x)

_∩_ : (P : A → Set ℓ) → (Q : A → Set ℓ) → A → Set ℓ
(P ∩ Q) x = (P x) × (Q x)

∪-minimal : (P : A → Set ℓ) → (Q : A → Set ℓ)
          → (R : A → Set ℓ) → P ⊆ R → Q ⊆ R
          → ((P ∪ Q) ⊆ R)
∪-minimal P Q R P⊆R _ (inj₁ x∈P) = P⊆R x∈P
∪-minimal P Q R _ Q⊆R (inj₂ x∈Q) = Q⊆R x∈Q

∩-maximal : (P : A → Set ℓ) → (Q : A → Set ℓ)
          → (R : A → Set ℓ) → R ⊆ P → R ⊆ Q
          → (R ⊆ (P ∩ Q))
∩-maximal P Q R R⊆P R⊆Q x∈R = ( R⊆P x∈R , R⊆Q x∈R)
