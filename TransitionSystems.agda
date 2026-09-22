module TransitionSystems where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (∃; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (_×_)
open import Relation.Binary.Definitions using (Symmetric; Transitive; Reflexive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; sym)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as ReflTrans
open import Function using (id; _∘_; _∘₂_) renaming (const to _˙)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe)
open import Data.Sum using (_⊎_)

-- Section Start Page 30

open import Level using (Level) renaming (zero to lzero; suc to lsuc)

record TransitionSystem {ℓ : Level} : Set (lsuc ℓ) where
    constructor ⌞_,_,_⌟
    field
        Γ : Set ℓ
        _⇒_ : Γ → Γ → Set
        T : (s : Γ) → Set

    variable
        s₁ s₂ s´ : Γ
        s´t : T s´

    open ReflTrans
        using (Star)
        renaming (ε to x⇒x; _◅_ to _⇒∘⇒*_)
        public


    -- INNER Section Begin Page 38. This label is place 2

    _⇒*_ = Star _⇒_

    length : s₁ ⇒* s₂ → ℕ
    length x⇒x = 0
    length (_ ⇒∘⇒* x₁) = suc (length x₁)

    _⇒⟨_⟩_ : (s₁ : Γ) (l : ℕ) (s₂ : Γ) → Set ℓ
    s₁ ⇒⟨ l ⟩ s₂ = Σ (s₁ ⇒* s₂) (λ x → length x ≡ l)

    private
        module changedFromOriginals where
            -- The original definition for these transition sequences
            -- uses a `k` to transition k amount of times.
            -- This reminds me of the Vec type, in the sense that
            -- a list is a generic length and vec is a determined length
            data _⇒⟨_⟩ᵇ_ : Γ → ℕ → Γ → Set ℓ where
                x⇒x : ∀ {γ} → γ ⇒⟨ 0 ⟩ᵇ γ
                _⇒∘⇒_ : ∀ {γ γ´ k γ˝}
                    → γ ⇒ γ˝
                    → γ˝ ⇒⟨ k ⟩ᵇ γ´
                    → γ ⇒⟨ suc k ⟩ᵇ γ´

            -- `b` stands for book. This is the book's definition
            -- which is annoying to prove stuff for since it caries a
            -- constant. The non-book version is proven to be equivalent
            _⇒*ᵇ_ : Γ → Γ → Set ℓ
            γ ⇒*ᵇ γ′ = ∃ λ k → γ ⇒⟨ k ⟩ᵇ γ′

            -- Proving they're isomorphic by making translation functions and proving they're purely invertible
            right : {x y : Γ} → x ⇒*ᵇ y → x ⇒* y
            right (_ , x⇒x) =  x⇒x
            right (_ , (_⇒∘⇒_ {k = k} x snd)) = x ⇒∘⇒* right (k , snd) -- x ⇒∘⇒* right (fst , snd)

            left : {x y : Γ} → x ⇒* y → x ⇒*ᵇ y
            left x⇒x = 0 , x⇒x
            left (x ⇒∘⇒* x₁) = suc (left x₁ .proj₁) , x ⇒∘⇒ (left x₁ .proj₂)

            rightInv : {x y : Γ} → (q : x ⇒* y) → right (left q) ≡ q
            rightInv x⇒x = refl
            rightInv (x ⇒∘⇒* q) = cong (x ⇒∘⇒*_) (rightInv q)

            leftInv : {x y : Γ} → (q : x ⇒*ᵇ y) → left (right q) ≡ q
            leftInv (ℕ.zero , x⇒x) = refl
            leftInv (fst , (_⇒∘⇒_ {k = k} x snd)) = cong (λ z → suc (z .proj₁) , (x ⇒∘⇒ (z .proj₂))) (leftInv (k , snd))


    _∘⇒*∘_ : ∀ {x y z}
          → x ⇒* y
          → y ⇒* z
          → x ⇒* z
    x⇒x ∘⇒*∘ x₁ = x₁
    (x ⇒∘⇒* x₂) ∘⇒*∘ x₁ = x ⇒∘⇒* (x₂ ∘⇒*∘ x₁)

    -- With old definition of ⇒* the implementation is uglier
    --      (0 , x⇒x) ∘⇒∘ x₁ = x₁
    --      (suc fst , x ⇒∘⇒ snd) ∘⇒∘ x₁ = x ⇒∘ ((fst , snd) ∘⇒∘ x₁)

    infixr 5 _⇒*_ _∘⇒*∘_

    -- INNER Section End Page 38

    -- Section End Page 30

    -- Section Begin Page 71

    -- Problem 5.7: Smallstep Semantic Equivalence
    -- Except I've generalized it to any transition sequence
    data _~ₛ_ {s´t : T s´} : Rel Γ ℓ where
        *~ₛ* : (s₁ ≢ s´ → s₁ ⇒* s´ → s₂ ≢ s´ × s₂ ⇒* s´) → (s₂ ≢ s´ → s₂ ⇒* s´ → s₁ ≢ s´ × s₁ ⇒* s´) → s₁ ~ₛ s₂


    -- Problem 5.7: _~ₛ_ is an equivalence relation.
    -- For agda, s´ cannot be assumed to exist, so I reformulated it to: Given any end-state, define an equivalence relation for transitions to it
    ~ₛequivalenceTo : IsEquivalence (_~ₛ_ {s´t = s´t})
    ~ₛequivalenceTo = record
        { refl  = *~ₛ* (λ z z₁ → z , z₁) (λ z z₁ → z , z₁)
        ; sym   = ~ₛ-sym
        ; trans = ~ₛ-trans
        }
        where
        ~ₛ-sym : Symmetric _~ₛ_
        ~ₛ-sym (*~ₛ* y z) = *~ₛ* z y

        ~ₛ-trans : Transitive _~ₛ_
        ~ₛ-trans (*~ₛ* b c) (*~ₛ* y z) = *~ₛ* (λ z₁ z₂ → y (b z₁ z₂ .proj₁) (b z₁ z₂ .proj₂)) (λ z₁ z₂ → c (z z₁ z₂ .proj₁) (z z₁ z₂ .proj₂))

    -- Section End Page 71
