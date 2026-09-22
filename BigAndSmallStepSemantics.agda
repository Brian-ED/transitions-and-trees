module BigAndSmallStepSemantics where

open import TransitionSystems using (TransitionSystem)
open import Level using (Level) renaming (suc to lsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.Core using (Rel; _⇔_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary.Definitions using (Symmetric; Transitive; Reflexive)
open import Function using (_∘_; id)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary using (¬_)
-- Section Start Page 31

record BigStepSemantics {ℓ : Level} (TS : TransitionSystem {ℓ}) : Set ℓ where
    constructor ⌈>
    open TransitionSystem TS
    field
        BigStepping : {x y : Γ} → x ⇒ y → T y
        BigSteppingL : {x y : Γ} → x ⇒ y → ¬ (T x)


    ⇒→⇒* : ∀ {x z} → x ⇒ z → x ⇒* z
    ⇒→⇒* p = p ⇒∘⇒* x⇒x

    -- Section End Page 31

    ⇒→≢ : ∀ {x z} → x ⇒ z → x ≢ z
    ⇒→≢ p c rewrite c = (BigSteppingL p) (BigStepping p)

    -- Section Begin Page 70

    -- I've generalized the bigstep equivalence to any transition sequence
    data _~ᵇ_ {s´ : Γ} : Rel Γ ℓ where
        *~ᵇ* : (s₁ ⇒ s´ → s₂ ⇒ s´) → (s₂ ⇒ s´ → s₁ ⇒ s´) → s₁ ~ᵇ s₂

    -- Equivalence between 1-stepping small step semantics and big step semantics
    ~ₛ⇔~ᵇ : (_~ₛ_ {s´} {s´t = s´t}) ⇔ (_~ᵇ_ {s´})
    ~ₛ⇔~ᵇ {s´} = ~ₛ⇒~ᵇ , ~ᵇ⇒~ₛ
        where
        ~ₛ⇒~ᵇ : s₁ ~ₛ s₂ → s₁ ~ᵇ s₂
        ~ₛ⇒~ᵇ (*~ₛ* {s₁} {s₂} r l) = *~ᵇ* a b
            where
            a : s₁ ⇒ s´ → s₂ ⇒ s´
            a x with r (⇒→≢ x) (x ⇒∘⇒* x⇒x)
            ... | ne , x⇒x = ⊥-elim (ne refl)
            ... | ne , x₁ ⇒∘⇒* x⇒x = x₁
            ... | ne , x₁ ⇒∘⇒* x₂ ⇒∘⇒* p = ⊥-elim (BigSteppingL x₂ (BigStepping x₁))

            b : s₂ ⇒ s´ → s₁ ⇒ s´
            b x with l (⇒→≢ x) (x ⇒∘⇒* x⇒x)
            ... | ne , x⇒x = ⊥-elim (ne refl)
            ... | ne , x₁ ⇒∘⇒* x⇒x = x₁
            ... | ne , x₁ ⇒∘⇒* x₂ ⇒∘⇒* p = ⊥-elim (BigSteppingL x₂ (BigStepping x₁))

        ~ᵇ⇒~ₛ : s₁ ~ᵇ s₂ → s₁ ~ₛ s₂
        ~ᵇ⇒~ₛ (*~ᵇ* {s₁} {s₂} r l) = *~ₛ* a b
            where
            a : s₁ ≢ s´ → s₁ ⇒* s´ → s₂ ≢ s´ × s₂ ⇒* s´
            a x x⇒x = ⊥-elim (x refl)
            a x (x₁ ⇒∘⇒* x⇒x) = ⇒→≢ (r x₁) , r x₁ ⇒∘⇒* x⇒x
            a x (x₁ ⇒∘⇒* x₂ ⇒∘⇒* p) = ⊥-elim (BigSteppingL x₂ (BigStepping x₁))

            b : s₂ ≢ s´ → s₂ ⇒* s´ → s₁ ≢ s´ × s₁ ⇒* s´
            b x x⇒x = ⊥-elim (x refl)
            b x (x₁ ⇒∘⇒* x⇒x) = ⇒→≢ (l x₁) , l x₁ ⇒∘⇒* x⇒x
            b x (x₁ ⇒∘⇒* x₂ ⇒∘⇒* p) = ⊥-elim (BigSteppingL x₂ (BigStepping x₁))


    ~ᵇequivalence : IsEquivalence (_~ᵇ_ {s´})
    ~ᵇequivalence = record
        { refl  = *~ᵇ* id id
        ; sym   = ~ᵇ-sym
        ; trans = ~ᵇ-trans
        }
        where
        ~ᵇ-sym : Symmetric _~ᵇ_
        ~ᵇ-sym (*~ᵇ* y z) = *~ᵇ* z y

        ~ᵇ-trans : Transitive _~ᵇ_
        ~ᵇ-trans (*~ᵇ* b c) (*~ᵇ* y z) = *~ᵇ* (λ z₁ → y (b z₁)) (λ z₁ → c (z z₁))

    -- Section End Page 70


    -- Section Begin Page 71


    -- Section End Page 71
