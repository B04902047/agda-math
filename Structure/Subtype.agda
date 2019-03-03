
module Structure.Subtype {a ℓ} {A : Set a} where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

_\[_] : (P : A → Set ℓ) → (Q : A → Set ℓ) → A → Set ℓ
P \[ Q ] = λ x → ((P x) × (¬ (Q x)))

data ⊤ : Set ℓ where
  true : ⊤

_⊆_ : (P : A → Set ℓ) → (Q : A → Set ℓ) → Set (a ⊔ ℓ)
P ⊆ Q = {x : A} → P x → Q x
