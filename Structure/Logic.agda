
module Structure.Logic where

open import Data.Product public
open import Relation.Nullary using (¬_) public
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]) public
open import Function using (id; _∘_) public
open import Data.Empty using (⊥-elim) public

_↔_ : ∀{a b} → Set a → Set b → Set _
X ↔ Y = (X → Y) × (Y → X)


A∨A→A : ∀ {a} → {A : Set a} → A ⊎ A → A
A∨A→A (inj₁ x) = x
A∨A→A (inj₂ x) = x

proj₃ : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
        → A × B × C → C
proj₃ (x , y , z) = z
