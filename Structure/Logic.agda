
module Structure.Logic where

open import Data.Product using (_×_; proj₁; proj₂; _,_) public
open import Relation.Nullary using (¬_) public

_↔_ : ∀{a b} → Set a → Set b → Set _
X ↔ Y = (X → Y) × (Y → X)
