
module Basic.Logic where

open import Data.Product public
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Unit using (⊤) public

open import Relation.Nullary using (¬_) public
open import Function using (id; _∘_) public


_↔_ : ∀{a b} → Set a → Set b → Set _
X ↔ Y = (X → Y) × (Y → X)

A∨A→A : ∀ {a} → {A : Set a} → A ⊎ A → A
A∨A→A (inj₁ x) = x
A∨A→A (inj₂ x) = x

contraposition : ∀ {a b} → {P : Set a} → {Q : Set b}
                → (P → Q) → ¬ Q → ¬ P
contraposition p→q ¬q p = ¬q (p→q p)

proj₃ : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
        → A × B × C → C
proj₃ (x , y , z) = z
