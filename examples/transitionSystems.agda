module examples.transitionSystems where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)

-- Section Start Page 30

data Γ₁ : Set where
    γ₁ : Γ₁
    γ₂ : Γ₁
    γ₃ : Γ₁
    γ₄ : Γ₁

_⇒₁_ : Γ₁ → Γ₁ → Set
γ₃ ⇒₁ y  = ⊥
x  ⇒₁ γ₃ = ⊤
x ⇒₁ y = ⊥

T₁_ : Γ₁ → Set
T₁ γ₁ = ⊥
T₁ γ₂ = ⊥
T₁ γ₃ = ⊤
T₁ γ₄ = ⊥

testSystem : TransitionSystem
testSystem = ⌞ Γ₁ , _⇒₁_ , T₁_ ⌟

-- Section End Page 30
