module Bims where

-- Section Start Page 29

module Aexp₁-bigstep-semantic where
    open import Data.String using () renaming (String to Var)
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    data Aexp₁ : Set where
        N_ : Num → Aexp₁
        -- V_ : Var → Aexp₁ -- The book decides to not define variables yet
        _+_ : Aexp₁ → Aexp₁ → Aexp₁
        _*_ : Aexp₁ → Aexp₁ → Aexp₁
        _-_ : Aexp₁ → Aexp₁ → Aexp₁
        [_] : Aexp₁ → Aexp₁

    data Bexp : Set where
        _==_ : Aexp₁ → Aexp₁ → Bexp
        _<_ : Aexp₁ → Aexp₁ → Bexp
        ¬_ : Bexp → Bexp
        _∧_ : Bexp → Bexp → Bexp
        ⟨_⟩ : Bexp → Bexp

    data Stm : Set where
        skip : Stm
        _←_ : Var → Aexp₁ → Stm
        _Å_ : Stm → Stm → Stm
        ifStm_then_else : Bexp → Stm → Stm → Stm
        _while_ : Stm → Bexp → Stm

    infixr 5 N_
    infixl 2 _Å_
    infixr 3 _*_
    infixr 4 _+_
    infixr 4 _-_

    -- Section End Page 29

    -- Section Start Page 30

    -- Section End Page 30

    -- Section Start Page 32-33
    -- 3.4.1 A big-step semantics of Aexp₁

    data _⇒₁_ : Aexp₁ ⊎ Num → Aexp₁ ⊎ Num → Set where
        _PLUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₁ α₁ ⇒₁ inj₂ v₁
                   → inj₁ α₂ ⇒₁ inj₂ v₂
                   → inj₁ (α₁ + α₂) ⇒₁ inj₂ (v₁ +ℤ v₂)

        _MINUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                    → inj₁ α₁ ⇒₁ inj₂ v₁
                    → inj₁ α₂ ⇒₁ inj₂ v₂
                    → inj₁ ( α₁ - α₂ ) ⇒₁ inj₂ (v₁ -ℤ v₂)

        _MULT-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₁ α₁ ⇒₁ inj₂ v₁
                   → inj₁ α₂ ⇒₁ inj₂ v₂
                   → inj₁ (α₁ * α₂) ⇒₁ inj₂ (v₁ *ℤ v₂)

        PARENT-BSS_ : ∀ {α₁ v₁}
                    → inj₁ α₁ ⇒₁ inj₂ v₁
                    → inj₁ [ α₁ ] ⇒₁ inj₂ v₁

        NUM-BSS : ∀ {n}
                → inj₁ (N n) ⇒₁ inj₂ n

    infixr 5 _PLUS-BSS_
    infixr 5 _MULT-BSS_
    infixr 5 _MINUS-BSS_
    infixr 5 PARENT-BSS_

    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import Data.Product using (_×_)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤)

    transitionSystem = ⌞ Γ , _⇒₁_ , T ⌟
        where
            Γ = Aexp₁ ⊎ Num
            T : Γ → Set
            T (inj₁ _) = ⊥
            T (inj₂ _) = ⊤

    open TransitionSystem transitionSystem public


-- Section End Page 32-33

-- Section Start Page 36-37
-- A small-step semantics of Aexp₁

module Aexp₁-smallstep-semantic where
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool)

    -- Need to redefine Aexp to support non-literals too...
    -- "The presentation becomes a little easier if we can let values appear directly
    -- in our intermediate results. We do this by extending the formation rules for
    -- Aexp such that values become elements of Aexp"
    data Aexp₁ss : Set where
        N_ : Num → Aexp₁ss -- Number literals
        V_ : Num → Aexp₁ss -- Number value
        _+_ : Aexp₁ss → Aexp₁ss → Aexp₁ss
        _*_ : Aexp₁ss → Aexp₁ss → Aexp₁ss
        _-_ : Aexp₁ss → Aexp₁ss → Aexp₁ss
        [_] : Aexp₁ss → Aexp₁ss

    data Bexpₛₛ : Set where
        _==_ : Aexp₁ss → Aexp₁ss → Bexpₛₛ
        _<_ : Aexp₁ss → Aexp₁ss → Bexpₛₛ
        ¬_ : Bexpₛₛ → Bexpₛₛ
        _∧_ : Bexpₛₛ → Bexpₛₛ → Bexpₛₛ
        ⟨_⟩ : Bexpₛₛ → Bexpₛₛ
        _ᵇ : Bool → Bexpₛₛ

    infixr 7 N_ V_
    infixr 6 _*_
    infixr 5 _+_
    infixr 5 _-_
    infix 4 _==_
    infix 3 _<_
    infixr 3 _∧_
    infix 2 _⇒₂_

    infixr 5 PLUS-1ₛₛₛ_
    infixr 5 PLUS-2ₛₛₛ_
    infixr 5 PLUS-3ₛₛₛ
    infixr 5 MULT-1ₛₛₛ_
    infixr 5 MULT-2ₛₛₛ_
    infixr 5 MULT-3ₛₛₛ
    infixr 5 SUB-1ₛₛₛ_
    infixr 5 SUB-2ₛₛₛ_
    infixr 5 SUB-3ₛₛₛ
    infixr 5 PARENT-1ₛₛₛ_
    infixr 5 NUMₛₛₛ

    data _⇒₂_ : Aexp₁ss → Aexp₁ss → Set where

        -- PLUS
        PLUS-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒₂ α₁´
                   → α₁ + α₂ ⇒₂ α₁´ + α₂

        PLUS-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒₂ α₂´
                   → α₁ + α₂ ⇒₂ α₁ + α₂´

        PLUS-3ₛₛₛ : ∀ {n₁ n₂}
                  → V n₁ + V n₂ ⇒₂ V (n₁ +ℤ n₂)

        -- MULT
        MULT-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒₂ α₁´
                   → α₁ * α₂ ⇒₂ α₁´ * α₂

        MULT-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒₂ α₂´
                   → α₁ * α₂ ⇒₂ α₁ * α₂´

        MULT-3ₛₛₛ : ∀ {v₁ v₂}
                  → V v₁ * V v₂ ⇒₂ V (v₁ *ℤ v₂)

        -- SUB
        SUB-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                  → α₁ ⇒₂ α₁´
                  → α₁ - α₂ ⇒₂ α₁´ - α₂

        SUB-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                  → α₂ ⇒₂ α₂´
                  → α₁ - α₂ ⇒₂ α₁ - α₂´

        SUB-3ₛₛₛ : ∀ {x y}
                 → V x - V y ⇒₂ V (x -ℤ y)

        -- PARENTHESES
        PARENT-1ₛₛₛ_ : ∀ {α α´} -- The book uses α₁ and α₁´, I don't know why it adds the ₁
                     → α ⇒₂ α´
                     → [ α ] ⇒₂ [ α´ ]

        PARENT-2ₛₛₛ_ : ∀ {x y}
                     → x ≡ y
                     → [ V x ] ⇒₂ V y

        -- NUM
        NUMₛₛₛ : ∀ {x}
                  → N x ⇒₂ V x

    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import Data.Product using (_×_)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤)

    transitionSystem = ⌞ Γ , _⇒₂_ , T ⌟
        where
            Γ = Aexp₁ss
            T : Γ → Set
            T (V _) = ⊤
            T _ = ⊥

    open TransitionSystem transitionSystem public

-- Section End Page 36-37

-- Section Begin Page 40

module Bexp-bigstep-transition where
    open Aexp₁-bigstep-semantic using (Bexp; _⇒₁_; _==_; _<_; ¬_; ⟨_⟩; _∧_)

    open import Data.Integer using () renaming (_<_ to _<ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff)


    data _⇒b_ : Bexp ⊎ Bool → Bexp ⊎ Bool → Set where

        EQUALS-1-BSS : ∀ {α₁ α₂ v₁ v₂}
                     → inj₁ α₁ ⇒₁ inj₂ v₁
                     → inj₁ α₂ ⇒₁ inj₂ v₂
                     → v₁ ≡ v₂
                     → inj₁ (α₁ == α₂) ⇒b inj₂ tt

        EQUALS-2-BSS : ∀ {α₁ α₂ v₁ v₂}
                     → inj₁ α₁ ⇒₁ inj₂ v₁
                     → inj₁ α₂ ⇒₁ inj₂ v₂
                     → not (v₁ ≡ v₂)
                     → inj₁ (α₁ == α₂) ⇒b inj₂ ff

        GREATERTHAN-1-BSS : ∀ {α₁ α₂ v₁ v₂}
                          → inj₁ α₁ ⇒₁ inj₂ v₁
                          → inj₁ α₂ ⇒₁ inj₂ v₂
                          → v₁ <ℤ v₂
                          → inj₁ (α₁ < α₂) ⇒b inj₂ ff

        GREATERTHAN-2-BSS : ∀ {α₁ α₂ v₁ v₂}
                          → inj₁ α₁ ⇒₁ inj₂ v₁
                          → inj₁ α₂ ⇒₁ inj₂ v₂
                          → not (v₁ <ℤ v₂)
                          → inj₁ (α₁ < α₂) ⇒b inj₂ ff

        NOT-1-BSS_ : ∀ {b}
                   → inj₁ b ⇒b inj₂ ff
                   → inj₁ (¬ b) ⇒b inj₂ tt

        NOT-2-BSS_ : ∀ {b}
                   → inj₁ b ⇒b inj₂ tt
                   → inj₁ (¬ b) ⇒b inj₂ ff

        PARENTH-B-BSS : ∀ {b v}
                      → inj₁ b ⇒b v
                      → inj₁ ⟨ b ⟩ ⇒b v

        AND-1-BSS : ∀ {b₁ b₂}
                  → inj₁ b₁ ⇒b inj₂ tt
                  → inj₁ b₂ ⇒b inj₂ tt
                  → inj₁ (b₁ ∧ b₂) ⇒b inj₂ tt

        AND-2-BSS : ∀ {b₁ b₂}
                  → (inj₁ b₁ ⇒b inj₂ ff)
                  ⊎ (inj₁ b₂ ⇒b inj₂ ff)
                  → inj₁ (b₁ ∧ b₂) ⇒b inj₂ ff

-- Problem 3.16
module Bexp-smallstep-transition where
    open Aexp₁-smallstep-semantic

    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _-ℤ_; _<_ to _<ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff; _∧_ to _∧b_)
    open import Data.Nat using (_≡ᵇ_)

    _==ℤ_ : Num → Num → Bool
    Num.pos x ==ℤ Num.pos y = x ≡ᵇ y
    Num.pos x ==ℤ Num.negsuc y = ff
    Num.negsuc x ==ℤ Num.pos y = ff
    Num.negsuc x ==ℤ Num.negsuc y = x ≡ᵇ y

    open import Data.Bool using (if_then_else_; Bool) renaming (true to tt; false to ff)

    infix 2 _⇒b_

    data _⇒b_ : Bexpₛₛ → Bexpₛₛ → Set where

        EQUALS-1-SSS : ∀ {α₁ α₁´ α₂}
                      → α₁ ⇒₂ α₁´
                      → α₁ == α₂ ⇒b α₁´ == α₂

        EQUALS-2-SSS : ∀ {α₁ α₂ α₂´}
                      → α₂ ⇒₂ α₂´
                      → α₁ == α₂ ⇒b α₁ == α₂´

        EQUALS-3-SSS : ∀ {x}
                     → V x == V x ⇒b tt ᵇ

        EQUALS-4-SSS : ∀ {x y}
                     → not x ≡ y
                     → V x == V y ⇒b ff ᵇ

        GREATERTHAN-1-SSS : ∀ {α₁ α₁´ α₂}
                           → α₁ ⇒₂ α₁´
                           → α₁ < α₂ ⇒b α₁´ < α₂

        GREATERTHAN-2-SSS : ∀ {α₁ α₂ α₂´}
                           → α₂ ⇒₂ α₂´
                           → α₁ < α₂ ⇒b α₁ < α₂´

        GREATERTHAN-3-SSS : ∀ {x y}
                          → x <ℤ y
                          → V x < V y ⇒b tt ᵇ

        GREATERTHAN-4-SSS : ∀ {x y}
                          → not x <ℤ y
                          → V x < V y ⇒b ff ᵇ

        NOT-1-SSS : ∀ {α α´}
                   → α ⇒b α´
                   → ¬ α ⇒b ¬ α´

        NOT-2-SSS : ¬ (ff ᵇ) ⇒b tt ᵇ

        NOT-3-SSS : ¬ (tt ᵇ) ⇒b ff ᵇ

        PARENTH-B-BSS : ∀ {α α´}
                      → α ⇒b α´
                      → ⟨ α ⟩ ⇒b ⟨ α´ ⟩

        AND-1-SSS : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒b α₁´
                   → α₁ ∧ α₂ ⇒b α₁´ ∧ α₂

        AND-2-SSS : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒b α₂´
                   → α₁ ∧ α₂ ⇒b α₁ ∧ α₂´

        AND-3-SSS : tt ᵇ ∧ tt ᵇ ⇒b tt ᵇ

        AND-4-SSS : ∀ {α}
                  → ff ᵇ ∧ α ⇒b ff ᵇ

        AND-5-SSS : ∀ {α}
                  → α ∧ ff ᵇ ⇒b ff ᵇ


-- Section End Page 40

module Aexp₂-semantic where
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _<_ to _<ℤ_)
    open import Data.String using () renaming (String to Var)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤) renaming (tt to ttt)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Agda.Builtin.Maybe using (Maybe; just; nothing)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff)

    open import Data.String using (String; _<_; _<?_; _==_)
    <<str = λ a b c → <-isStrictPartialOrder-≈ .trans {a} {b} {c}
        where
            open import Relation.Binary.Structures using (IsStrictPartialOrder)
            open IsStrictPartialOrder using (trans)
            open import Data.String.Properties using (<-isStrictPartialOrder-≈)

    open import States Num String _<_ <<str _<?_ _==_ using (States; _[_↦_]; lookup)

    -- Section Start Page 44-45

    infixr 5 N_
    infixr 3 _*_
    infixr 4 _+_
    infixr 4 _-_

    infixr 5 _PLUS-BSS_
    infixr 5 _MULT-BSS_
    infixr 5 _MINUS-BSS_
    infixr 5 PARENT-BSS_

    data Aexp₂ : Set where
        N_ : Num → Aexp₂ -- Number literals
        V_ : Var → Aexp₂
        _+_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Aexp₂
        _*_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Aexp₂
        _-_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Aexp₂
        [_] : Aexp₂ ⊎ Num → Aexp₂


    data _⊢_⇒ₐ_ : States → Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Set where
        _PLUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                   → s ⊢ α₁ ⇒ₐ inj₂ v₁
                   → s ⊢ α₂ ⇒ₐ inj₂ v₂
                   → s ⊢ inj₁ (α₁ + α₂) ⇒ₐ inj₂ (v₁ +ℤ v₂)

        _MINUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                    → s ⊢ α₁ ⇒ₐ inj₂ v₁
                    → s ⊢ α₂ ⇒ₐ inj₂ v₂
                    → s ⊢ inj₁ ( α₁ - α₂ ) ⇒ₐ inj₂ (v₁ -ℤ v₂)

        _MULT-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                   → s ⊢ α₁ ⇒ₐ inj₂ v₁
                   → s ⊢ α₂ ⇒ₐ inj₂ v₂
                   → s ⊢ inj₁ (α₁ * α₂) ⇒ₐ inj₂ (v₁ *ℤ v₂)

        PARENT-BSS_ : ∀ {s α₁ v₁}
                    → s ⊢ α₁ ⇒ₐ inj₂ v₁
                    → s ⊢ inj₁ [ α₁ ] ⇒ₐ inj₂ v₁

        NUM-BSS : ∀ {s n}
                → s ⊢ inj₁ (N n) ⇒ₐ inj₂ n

        VAR-BSS_ : ∀ {s x v}
                 → (lookup s x) ≡ just v
                 → s ⊢ inj₁ (V x) ⇒ₐ inj₂ v

    -- The book states that the `⌞ (Aexp₂ ⊎ Num) , (_⊢_⇒ₐ_ s) , T₃ ⌟` transition system is a big-step-semantic, though does not prove it.
    -- Here is a proof for any starting States s:

    T₃ : Aexp₂ ⊎ Num → Set
    T₃ (inj₂ x) = ⊤
    T₃ (inj₁ x) = ⊥

    Aexp₂Semantic : States → TransitionSystem
    Aexp₂Semantic s = ⌞ Aexp₂ ⊎ Num , _⊢_⇒ₐ_ s , T₃ ⌟

    Aexp₂-is-big-step-proof : ∀ s {x y} → s ⊢ x ⇒ₐ y → T₃ y
    Aexp₂-is-big-step-proof _ {_} {inj₂ _} _ = ttt

    open import Relation.Nullary.Negation using (¬_)
    open import Relation.Binary.PropositionalEquality using (refl)

    Aexp₂-is-big-step-proof2 : ∀ s {x y} → s ⊢ x ⇒ₐ y → ¬ T₃ x
    Aexp₂-is-big-step-proof2 _ {inj₁ _} _ = λ ()

    Aexp₂big-semantic : ∀ s → BigStepSemantics (Aexp₂Semantic s)
    Aexp₂big-semantic s = ⌈> (Aexp₂-is-big-step-proof s) (Aexp₂-is-big-step-proof2 s)

    -- Section End Page 44-45

    -- Section Begin Page 46

    data Bexp₂ : Set where
        _==₃_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Bexp₂
        _<₃_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Bexp₂
        ¬₃_ : Bexp₂ → Bexp₂
        _∧₃_ : Bexp₂ → Bexp₂ → Bexp₂
        ⟨_⟩₃ : Bexp₂ → Bexp₂
        _ᵇ : Bool → Bexp₂

    infix 21 _ᵇ ¬₃_

    data _⊢_⇒₂b_ : States → Bexp₂ → Bexp₂ → Set where

        _EQUAL-1-BSS_ : ∀ {s α₁ α₂ v}
                      → s ⊢ α₁ ⇒ₐ inj₂ v
                      → s ⊢ α₂ ⇒ₐ inj₂ v
                      → s ⊢ α₁ ==₃ α₂ ⇒₂b tt ᵇ

        EQUALS-2-BSS : ∀ {s α₁ α₂ v₁ v₂}
                     → s ⊢ α₁ ⇒ₐ inj₂ v₁
                     → s ⊢ α₂ ⇒ₐ inj₂ v₂
                     → not (v₁ ≡ v₂)
                     → s ⊢ α₁ ==₃ α₂ ⇒₂b ff ᵇ

        GREATERTHAN-1-BSS : ∀ {s α₁ α₂ v₁ v₂}
                          → s ⊢ α₁ ⇒ₐ inj₂ v₁
                          → s ⊢ α₂ ⇒ₐ inj₂ v₂
                          → v₁ <ℤ v₂
                          → s ⊢ α₁ <₃ α₂ ⇒₂b tt ᵇ

        GREATERTHAN-2-BSS : ∀ {s α₁ α₂ v₁ v₂}
                          → s ⊢ α₁ ⇒ₐ inj₂ v₁
                          → s ⊢ α₂ ⇒ₐ inj₂ v₂
                          → not (v₁ <ℤ v₂)
                          → s ⊢ α₁ <₃ α₂ ⇒₂b ff ᵇ

        NOT-1-BSS_ : ∀ {s b}
                   → s ⊢ b ⇒₂b ff ᵇ
                   → s ⊢ ¬₃ b ⇒₂b tt ᵇ

        NOT-2-BSS_ : ∀ {s b}
                   → s ⊢ b ⇒₂b tt ᵇ
                   → s ⊢ ¬₃ b ⇒₂b ff ᵇ

        PARENTH-B-BSS : ∀ {s b v}
                      → s ⊢ b ⇒₂b v
                      → s ⊢ ⟨ b ⟩₃ ⇒₂b v

        AND-1-BSS : ∀ {s b₁ b₂}
                  → s ⊢ b₁ ⇒₂b tt ᵇ
                  → s ⊢ b₂ ⇒₂b tt ᵇ
                  → s ⊢ b₁ ∧₃ b₂ ⇒₂b tt ᵇ

        AND-2-BSS : ∀ {s b₁ b₂}
                  → (s ⊢ b₁ ⇒₂b ff ᵇ)
                  → s ⊢ b₁ ∧₃ b₂ ⇒₂b ff ᵇ

        AND-3-BSS : ∀ {s b₁ b₂}
                  → (s ⊢ b₂ ⇒₂b ff ᵇ)
                  → s ⊢ b₁ ∧₃ b₂ ⇒₂b ff ᵇ

    -- Section End Page 46


module Stm₂-semantic where
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _<_ to _<ℤ_)
    open import Data.String using () renaming (String to Var)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤) renaming (tt to ttt)
    open import Relation.Nullary.Negation using (¬_)
    open import Agda.Builtin.Maybe using (Maybe; just; nothing)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff)
    open import Data.Product using (_×_)
    open Aexp₂-semantic using (Aexp₂; Bexp₂; _⊢_⇒ₐ_; _⊢_⇒₂b_; _ᵇ)

    open import Data.String using (String; _<_; _<?_; _==_)
    <<str = λ a b c → <-isStrictPartialOrder-≈ .trans {a} {b} {c}
        where
            open import Relation.Binary.Structures using (IsStrictPartialOrder)
            open IsStrictPartialOrder using (trans)
            open import Data.String.Properties using (<-isStrictPartialOrder-≈)

    open import States Num String _<_ <<str _<?_ _==_ using (States; _[_↦_])


    -- Section Begin Page 47

    data Stm₂ : Set where
        skip₂ : Stm₂
        _←₂_ : Var → Aexp₂ ⊎ Num → Stm₂
        _Å₂_ : Stm₂ → Stm₂ → Stm₂
        ifStm₂_then_else_ : Bexp₂ → Stm₂ → Stm₂ → Stm₂
        while_do₂_ : Bexp₂ → Stm₂ → Stm₂

    data ⟨_,_⟩⇒₂_ : Stm₂ → States → States → Set where
        ASS-BSS         : ∀ {x a s v}
                        → s ⊢ a ⇒ₐ inj₂ v
                        → ⟨ (x ←₂ a) , s ⟩⇒₂ (s [ x ↦ v ])

        SKIP-BSS        : ∀ {s}
                        → ⟨ skip₂ , s ⟩⇒₂ s

        COMP-BSS        : ∀ {S₁ S₂ s s´ s˝}
                        → ⟨ S₁ , s ⟩⇒₂ s˝
                        → ⟨ S₂ , s˝ ⟩⇒₂ s´
                        → ⟨ (S₁ Å₂ S₂) , s ⟩⇒₂ s´

        IF-TRUE-BSS     : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₁ , s ⟩⇒₂ s´
                        → s ⊢ b ⇒₂b tt ᵇ
                        → ⟨ (ifStm₂ b then S₁ else S₂) , s ⟩⇒₂ s´

        IF-FALSE-BSS    : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₂ , s ⟩⇒₂ s´
                        → s ⊢ b ⇒₂b ff ᵇ
                        → ⟨ (ifStm₂ b then S₁ else S₂) , s ⟩⇒₂ s´

        WHILE-TRUE-BSS  : ∀ {S s s´ s˝ b}
                        → s ⊢ b ⇒₂b tt ᵇ
                        → ⟨ S , s ⟩⇒₂ s˝
                        → ⟨ (while b do₂ S) , s˝ ⟩⇒₂ s´
                        → ⟨ (while b do₂ S) , s ⟩⇒₂ s´

        WHILE-FALSE-BSS : ∀ {S s b}
                        → s ⊢ b ⇒₂b ff ᵇ
                        → ⟨ (while b do₂ S) , s ⟩⇒₂ s

    -- Section End Page 47

    -- Section Begin Page 53
    open import Data.Product using (_×_; _,_)
    data ⟨_⟩⇒₂⟨_⟩ : (Stm₂ × States) ⊎ States → (Stm₂ × States) ⊎ States → Set where
        ASSₛₛₛ : ∀ {x a v s}
               → s ⊢ a ⇒ₐ inj₂ v
               → ⟨ inj₁ (x ←₂ a , s) ⟩⇒₂⟨ inj₂ (s [ x ↦ v ]) ⟩

        SKIPₛₛₛ : ∀ {s}
                → ⟨ inj₁ (skip₂ , s) ⟩⇒₂⟨ inj₂ s ⟩

        COMP-1ₛₛₛ : ∀ {s s´ S₁ S₁´ S₂}
                  → ⟨ inj₁ (S₁ , s) ⟩⇒₂⟨ inj₁ (S₁´ , s´) ⟩
                  → ⟨ inj₁ (S₁ Å₂ S₂ , s) ⟩⇒₂⟨ inj₁ (S₁´ Å₂ S₂ , s´) ⟩

        COMP-2ₛₛₛ : ∀ {s s´ S₁ S₂}
                  → ⟨ inj₁ (S₁ , s) ⟩⇒₂⟨ inj₂ s´ ⟩
                  → ⟨ inj₁ (S₁ Å₂ S₂ , s) ⟩⇒₂⟨ inj₁ (S₂ , s´) ⟩

        IF-TRUEₛₛₛ : ∀ {s b S₁ S₂}
                   → s ⊢ b ⇒₂b tt ᵇ
                   → ⟨ inj₁ (ifStm₂ b then S₁ else S₂ , s) ⟩⇒₂⟨ inj₁ (S₁ , s) ⟩

        IF-FALSEₛₛₛ : ∀ {s b S₁ S₂}
                    → s ⊢ b ⇒₂b ff ᵇ
                    → ⟨ inj₁ (ifStm₂ b then S₁ else S₂ , s) ⟩⇒₂⟨ inj₁ (S₂ , s) ⟩

        WHILEₛₛₛ : ∀ {s b S}
                 → ⟨ inj₁ (while b do₂ S , s) ⟩⇒₂⟨ inj₁ (ifStm₂ b then S Å₂ (while b do₂ S) else skip₂ , s) ⟩

    ⟨_⟩⇒₂⟨_⟩-transition = ⌞ Γ , ⟨_⟩⇒₂⟨_⟩ , T ⌟
        where
            Γ = (Stm₂ × States) ⊎ States
            T : Γ → Set
            T (inj₁ x) = ⊥
            T (inj₂ y) = ⊤

    -- Imported via: open TransitionSystem ⟨_⟩⇒₂⟨_⟩-transition public

    -- Section End Page 53

-- Section Begin Page 65

module Stm₃-bss-semantic where
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _<_ to _<ℤ_)
    open import Data.String using () renaming (String to Var)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤) renaming (tt to ttt)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Agda.Builtin.Maybe using (Maybe; just; nothing)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff)
    open import Data.Product using (_×_; _,_)

    open import Data.String using (String; _<_; _<?_; _==_)
    <<str = λ a b c → <-isStrictPartialOrder-≈ .trans {a} {b} {c}
        where
            open import Relation.Binary.Structures using (IsStrictPartialOrder)
            open IsStrictPartialOrder using (trans)
            open import Data.String.Properties using (<-isStrictPartialOrder-≈)

    open import States Num String _<_ <<str _<?_ _==_ using (States; _[_↦_])

    open Aexp₂-semantic using (Aexp₂; Bexp₂; _⊢_⇒ₐ_; _⊢_⇒₂b_; _ᵇ; ¬₃_; NOT-2-BSS_; NOT-1-BSS_)

    data Stm₃ : Set where
        skip₃ : Stm₃
        _←₃_ : Var → Aexp₂ ⊎ Num → Stm₃
        _Å₃_ : Stm₃ → Stm₃ → Stm₃
        ifStm₃_then_else_ : Bexp₂ → Stm₃ → Stm₃ → Stm₃
        while_do₃_ : Bexp₂ → Stm₃ → Stm₃
        repeat_until_ : Stm₃ → Bexp₂ → Stm₃

    Γ = Stm₃ × States ⊎ States

    -- Table 5.1
    data ⟨_⟩⇒_ : Γ → Γ → Set
    ⟨_⟩⇒₂_ : (IN : Stm₃ × States) → (OUT : States) → Set
    ⟨ S ⟩⇒₂ s´ = ⟨ inj₁ S ⟩⇒ inj₂ s´
    data ⟨_⟩⇒_ where

        ASS-BSS         : ∀ {x a s v}
                        → s ⊢ a ⇒ₐ inj₂ v
                        → ⟨ x ←₃ a , s ⟩⇒₂ (s [ x ↦ v ])

        SKIP-BSS        : ∀ {s}
                        → ⟨ skip₃ , s ⟩⇒₂ s

        COMP-BSS        : ∀ {S₁ S₂ s s´ s˝}
                        → ⟨ S₁ , s ⟩⇒₂ s˝
                        → ⟨ S₂ , s˝ ⟩⇒₂ s´
                        → ⟨ S₁ Å₃ S₂ , s ⟩⇒₂ s´

        IF-TRUE-BSS     : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₁ , s ⟩⇒₂ s´
                        → s ⊢ b ⇒₂b tt ᵇ
                        → ⟨ (ifStm₃ b then S₁ else S₂) , s ⟩⇒₂ s´

        IF-FALSE-BSS    : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₂ , s ⟩⇒₂ s´
                        → s ⊢ b ⇒₂b ff ᵇ
                        → ⟨ (ifStm₃ b then S₁ else S₂) , s ⟩⇒₂ s´

        WHILE-TRUE-BSS  : ∀ {S s s´ s˝ b}
                        → s ⊢ b ⇒₂b tt ᵇ
                        → ⟨ S , s ⟩⇒₂ s˝
                        → ⟨ (while b do₃ S) , s˝ ⟩⇒₂ s´
                        → ⟨ (while b do₃ S) , s ⟩⇒₂ s´

        WHILE-FALSE-BSS : ∀ {S s b}
                        → s ⊢ b ⇒₂b ff ᵇ
                        → ⟨ (while b do₃ S) , s ⟩⇒₂ s

        REPEAT-TRUE-BSS : ∀ {S b s s´}
                          → ⟨ S , s ⟩⇒₂ s´
                          → s´ ⊢ b ⇒₂b tt ᵇ
                          → ⟨ repeat S until b , s ⟩⇒₂ s´

        REPEAT-FALSE-BSS : ∀ {S b s s´ s˝}
                          → ⟨ S , s ⟩⇒₂ s´
                          → s´ ⊢ b ⇒₂b ff ᵇ
                          → ⟨ repeat S until b , s´ ⟩⇒₂ s˝
                          → ⟨ repeat S until b , s ⟩⇒₂ s˝

    ⟨_⟩⇒₂⟨_⟩-transition = ⌞ Γ , ⟨_⟩⇒_ , T ⌟
        where
            T : Γ → Set
            T (inj₁ x) = ⊥
            T (inj₂ y) = ⊤

    -- Theorem 5.2 For all s ∈ States we have 〈repeat S until b, s〉 → s′ if and only if 〈S; while ¬b do S, s〉 → s′

    open import Data.Product using (proj₁; proj₂)

    A = λ S b s´ s → ⟨ repeat S until b , s ⟩⇒₂ s´
    B = λ S b s´ s → ⟨ S Å₃ (while ¬₃ b do₃ S) , s ⟩⇒₂ s´
    theoremLeft : ∀ {S b s s´} → A S b s´ s → B S b s´ s
    theoremLeft {S} {b} {s} {s´} (REPEAT-TRUE-BSS x x₁) = COMP-BSS x (WHILE-FALSE-BSS (NOT-2-BSS x₁))
    theoremLeft {S} {b} {s} {s´} (REPEAT-FALSE-BSS {s´ = s´₂} x x₁ x₂) with theoremLeft x₂
    ... | COMP-BSS p p₁ = COMP-BSS x (WHILE-TRUE-BSS (_⊢_⇒₂b_.NOT-1-BSS x₁) p p₁)

    theoremRight : ∀ {S b s s´} → B S b s´ s → A S b s´ s
    theoremRight {S} {b} {s} {s´} (COMP-BSS x y) = theoremRightMinor x y
        where
            -- To avoid a failed termination check by Agda, I made a minor version
            -- which separates the COMP-BSS into two arguments, making Agda happy
            theoremRightMinor : ∀ {S b s s´ s˝} → ⟨ S , s ⟩⇒₂ s´ → ⟨(while ¬₃ b do₃ S) , s´ ⟩⇒₂ s˝ → ⟨ repeat S until b , s ⟩⇒₂ s˝
            theoremRightMinor {S} {b} {s} {s´} {s˝} x (WHILE-FALSE-BSS (NOT-2-BSS x₁)) = REPEAT-TRUE-BSS x x₁
            theoremRightMinor {S} {b} {s} {s´} {s˝} x (WHILE-TRUE-BSS (NOT-1-BSS x₁) x₂ x₃) = REPEAT-FALSE-BSS x x₁ (theoremRightMinor x₂ x₃)

-- Section End Page 65
