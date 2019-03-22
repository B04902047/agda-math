
module Basic.Subtype {A : Set} where

open import Basic.Logic

nonProper : A → Set
nonProper _ = ⊤

trivial : A → Set
trivial _ = ⊥

_\[_] : (P : A → Set) → (Q : A → Set) → A → Set
P \[ Q ] = λ x → ((P x) × (¬ (Q x)))

_⊆_ : (P : A → Set) → (Q : A → Set) → Set
P ⊆ Q = {x : A} → P x → Q x

_∪_ : (P : A → Set) → (Q : A → Set) → A → Set
(P ∪ Q) x = (P x) ⊎ (Q x)

_∩_ : (P : A → Set) → (Q : A → Set) → A → Set
(P ∩ Q) x = (P x) × (Q x)

∪-minimal : (P : A → Set) → (Q : A → Set)
          → (R : A → Set) → P ⊆ R → Q ⊆ R
          → ((P ∪ Q) ⊆ R)
∪-minimal P Q R P⊆R _ (inj₁ x∈P) = P⊆R x∈P
∪-minimal P Q R _ Q⊆R (inj₂ x∈Q) = Q⊆R x∈Q

∩-maximal : (P : A → Set) → (Q : A → Set)
          → (R : A → Set) → R ⊆ P → R ⊆ Q
          → (R ⊆ (P ∩ Q))
∩-maximal P Q R R⊆P R⊆Q x∈R = ( R⊆P x∈R , R⊆Q x∈R)
