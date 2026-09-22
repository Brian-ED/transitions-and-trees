module examples.bigAndSmallStepSemantics where

open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import BigAndSmallStepSemantics using (BigStepSemantics; ⌈>)
open import examples.transitionSystems using (Γ₁; T₁_)

-- Section Start Page 31

_⇒₂_ : Γ₁ → Γ₁ → Set
x ⇒₂ Γ₁.γ₁ = ⊥
x ⇒₂ Γ₁.γ₂ = ⊥
Γ₁.γ₃ ⇒₂ Γ₁.γ₃ = ⊥
x ⇒₂ Γ₁.γ₃ = ⊤
x ⇒₂ Γ₁.γ₄ = ⊥

semantic : TransitionSystem
semantic = ⌞ Γ₁ , _⇒₂_ , T₁_ ⌟

semantic-is-big-step-proof : {x y : Γ₁} → (x ⇒₂ y) → (T₁ y)
semantic-is-big-step-proof {_} {Γ₁.γ₁} = λ ()
semantic-is-big-step-proof {_} {Γ₁.γ₂} = λ ()
semantic-is-big-step-proof {_} {Γ₁.γ₃} = λ _ → Data.Unit.tt
semantic-is-big-step-proof {_} {Γ₁.γ₄} = λ ()

open import Relation.Nullary.Negation using (¬_)

semantic-is-big-step-proof2 : {x y : Γ₁} → (x ⇒₂ y) → (¬ T₁ x)
semantic-is-big-step-proof2 {Γ₁.γ₁} _ = λ ()
semantic-is-big-step-proof2 {Γ₁.γ₂} _ = λ ()
semantic-is-big-step-proof2 {Γ₁.γ₄} {Γ₁.γ₃} x = λ ()
semantic-is-big-step-proof2 {Γ₁.γ₃} {Γ₁.γ₃} = λ ()
semantic-is-big-step-proof2 {Γ₁.γ₄} _ = λ x₁ → x₁

big-semantic : BigStepSemantics semantic
big-semantic = ⌈> semantic-is-big-step-proof semantic-is-big-step-proof2

-- Section End Page 31
