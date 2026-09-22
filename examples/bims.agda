module examples.bims where

-- Section Start Page 29
module Aexp₁-example-expr where
    open import Data.Integer using (+_)
    import Bims
    open Bims.Aexp₁-bigstep-semantic using (Aexp₁; _+_; N_; _*_)

    exprPg29 : Aexp₁
    exprPg29 = (N + 3 + N + 4) * (N + 14 + N + 9)
-- Section End Page 29

-- Section Start Page 32-33
-- 3.4.1 A big-step semantics of Aexp₁
module Aexp₁-is-big-step where
    import Bims
    open Bims.Aexp₁-bigstep-semantic
    open import Data.Integer using () renaming (ℤ to Num)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤) renaming (tt to ttt)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)

    Γ₁ = Aexp₁ ⊎ Num

    T₁ : (Aexp₁ ⊎ Num → Set)
    T₁ (inj₁ x) = ⊥
    T₁ (inj₂ x) = ⊤

    Aexp₁Semantic : TransitionSystem
    Aexp₁Semantic = ⌞ Γ₁ , _⇒₁_ , T₁ ⌟

    Aexp₁-is-big-step-proof : s₁ ⇒₁ s₂ → T₁ s₂
    Aexp₁-is-big-step-proof {inj₂ x} {inj₂ y} = λ z → ttt
    Aexp₁-is-big-step-proof {inj₁ x} {inj₂ y} = λ z → ttt
    Aexp₁-is-big-step-proof {x} {inj₁ y} ()

    open import Relation.Nullary.Negation renaming (¬_ to not_)
    Aexp₁-is-big-step-proof2 : s₁ ⇒₁ s₂ → not (T₁ s₁)
    Aexp₁-is-big-step-proof2 {inj₂ x} {inj₂ y} = λ ()
    Aexp₁-is-big-step-proof2 {inj₁ x} {inj₂ y} = λ z ()
    Aexp₁-is-big-step-proof2 {x} {inj₁ y} ()

    Aexp₁big-semantic : BigStepSemantics Aexp₁Semantic
    Aexp₁big-semantic = ⌈> Aexp₁-is-big-step-proof Aexp₁-is-big-step-proof2

-- Section End Page 32-33


-- Section Start Page 36-37
-- A small-step semantics of Aexp₁
module Aexp₁-small-step-semantic where
    open import Bims
    open Aexp₁-smallstep-semantic
    open import Data.Unit using (⊤)
    open import Data.Empty using (⊥)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Integer using () renaming (ℤ to Num)

    Aexp₁ssSemantic : TransitionSystem
    Aexp₁ssSemantic = ⌞ Aexp₁ss , _⇒₂_ , T₁ ⌟
        where
            Γ₁ = Aexp₁ss
            T₁ : Γ₁ → Set
            T₁ (N x) = ⊤
            T₁ x = ⊥

-- Section End Page 36-37

-- Section Begin Page 40
-- Test for solution to problem 3.16, small-step transition for Bexp
module Bexp-small-step-example where
    open import Relation.Binary.PropositionalEquality using (refl)
    import Bims
    open Bims.Aexp₁-smallstep-semantic using (Aexp₁ss; Bexpₛₛ; _ᵇ; N_; V_; _*_; _+_; NUMₛₛₛ; _∧_; _==_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff; _∧_ to _∧b_)
    open import Data.Integer using (+_) renaming (ℤ to Num)
    open import Data.Nat using (ℕ)

    infixr 4 _ₙ==_
    _ₙ==_ : ℕ → ℕ → Bexpₛₛ
    x ₙ== y = V + x == V + y

    infixr 4 _ₛ==_
    _ₛ==_ : ℕ → ℕ → Bexpₛₛ
    x ₛ== y = N + x == N + y

    ᵥtt : Bexpₛₛ
    ᵥtt = tt ᵇ
    ᵥff : Bexpₛₛ
    ᵥff = ff ᵇ

    code1 : Bexpₛₛ
    code1 = 0 ₙ== 1 ∧ 0 ₙ== 0 ∧ 6 ₛ== 5
    code2 = ᵥff     ∧ 0 ₙ== 0 ∧ 6 ₛ== 5
    code3 = ᵥff     ∧ ᵥtt     ∧ 6 ₛ== 5
    code4 = ᵥff     ∧ ᵥtt     ∧ ((N + 6) == (V (+ 5)))
    code5 = ᵥff     ∧ ᵥtt     ∧ 6 ₙ== 5
    code6 = ᵥff     ∧ ᵥtt     ∧ ᵥff
    code7 = ᵥff


    open Bims.Bexp-smallstep-transition
    a : code1 ⇒b code2
    a = AND-1-SSS (EQUALS-4-SSS λ ())
    b : code2 ⇒b code3
    b = AND-2-SSS (AND-1-SSS EQUALS-3-SSS)
    c : code3 ⇒b code4
    c = AND-2-SSS (AND-2-SSS (EQUALS-2-SSS NUMₛₛₛ))
    d : code4 ⇒b code5
    d = AND-2-SSS (AND-2-SSS (EQUALS-1-SSS NUMₛₛₛ))
    e : code5 ⇒b code6
    e = AND-2-SSS (AND-2-SSS (EQUALS-4-SSS λ ()))
    g : code6 ⇒b code7
    g = AND-4-SSS

-- Section End Page 4

-- Section Begin Page 48-52
module Aexp₂-state-transition-example where
    open import Relation.Binary.PropositionalEquality using (refl)
    import Bims
    open Bims.Aexp₂-semantic
    open Bims.Stm₂-semantic hiding (<<str)
    open import Data.Nat using (ℕ)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.List.Fresh using ([])

    open import Data.Integer using (ℤ; +_)
    open import Data.String using (String; _<_; _<?_; _==_)
    open import States ℤ String _<_ <<str _<?_ _==_

    code = ("i" ←₂ (inj₁ (N + 6))) Å₂
        (while ¬₃ (inj₁ (V "i") ==₃ inj₁ (N + 0)) do₂ (
            ("x" ←₂ inj₁(inj₁(V "x") + (inj₁(V "i")))) Å₂
            ("i" ←₂ inj₁(inj₁(V "i") - inj₁(N + 2)))
        ))

    beginState = [] [ "x" ↦ + 5 ]
    endState = ([] [ "x" ↦ + 17 ]) [ "i" ↦ + 0 ]
    P2 : ⟨ code , beginState ⟩⇒₂ endState
    P2 = COMP-BSS
        (ASS-BSS NUM-BSS)
        (WHILE-TRUE-BSS
            (NOT-1-BSS EQUALS-2-BSS (VAR-BSS refl) NUM-BSS λ())
            (COMP-BSS (ASS-BSS ((VAR-BSS refl) PLUS-BSS (VAR-BSS refl))) (ASS-BSS ((VAR-BSS refl) MINUS-BSS NUM-BSS)))
            (WHILE-TRUE-BSS
                (NOT-1-BSS EQUALS-2-BSS (VAR-BSS refl) NUM-BSS λ())
                (COMP-BSS (ASS-BSS ((VAR-BSS refl) PLUS-BSS (VAR-BSS refl))) (ASS-BSS ((VAR-BSS refl) MINUS-BSS NUM-BSS)))
                (WHILE-TRUE-BSS
                    (NOT-1-BSS EQUALS-2-BSS (VAR-BSS refl) NUM-BSS λ())
                    (COMP-BSS (ASS-BSS ((VAR-BSS refl) PLUS-BSS (VAR-BSS refl))) (ASS-BSS ((VAR-BSS refl) MINUS-BSS NUM-BSS)))
                    (WHILE-FALSE-BSS (NOT-2-BSS ((VAR-BSS refl) EQUAL-1-BSS NUM-BSS)))
                )
            )
        )

    -- Section Begin Page 52
    -- Problem 4.8
    open import Data.Product using (∃; _,_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Empty using (⊥)

    S = while inj₁(N + 0) ==₃ inj₁(N + 0) do₂ skip₂

    neverTerminates : ∀ s → ∃ λ s´ → not ⟨ S , s ⟩⇒₂ s´
    neverTerminates s = [] , f
        where
            f : {s : States} → ⟨ S , s ⟩⇒₂ [] → ⊥
            f (WHILE-TRUE-BSS _ _ x₂) = f x₂
            f (WHILE-FALSE-BSS (EQUALS-2-BSS NUM-BSS NUM-BSS x₃)) = x₃ refl

    -- Section End Page 52

-- Section End Page 48-52

-- Section Begin Page 54
-- Problem 4.9

module Aexp₂-smallstep-example where
    open import Relation.Binary.PropositionalEquality using (refl)
    import Bims
    open Bims.Aexp₂-semantic
    open Bims.Stm₂-semantic hiding (<<str)
    import TransitionSystems as TS
    open import Data.Nat using (ℕ; z≤n) renaming (s≤s to s≤s_)
    open import Data.Integer using (+_) renaming (+<+ to +<+_; ℤ to Num)
    open import Data.String using (String)
    open import Data.Product using (_,_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    open import Data.Integer using (ℤ; +_)
    open import Data.String using (String; _<_; _<?_; _==_)
    open import States ℤ String _<_ <<str _<?_ _==_
    open import Data.List.Fresh using ([])

    S =
        ifStm₂
            inj₁(N + 3) <₃ inj₁(V "x")
        then
            (
                ("x" ←₂ inj₁(inj₁(N + 3) + inj₁(V "x"))) Å₂
                ("y" ←₂ inj₁(N + 4))
            )
        else skip₂
    s = [] [ "x" ↦ + 4 ]

    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

    open TS.TransitionSystem ⟨_⟩⇒₂⟨_⟩-transition using (_⇒⟨_⟩_)
    open TS.TransitionSystem using (_⇒∘⇒*_; x⇒x)
    open import Data.Bool using (true)

    -- Problem 4.9
    -- There's only one transition from the start state
    transition1 :
        inj₁ (S , s )
        ⇒⟨ 1 ⟩
        inj₁ ((
            ("x" ←₂ inj₁(inj₁(N + 3) + inj₁(V "x"))) Å₂
            ("y" ←₂ inj₁(N + 4))
        ) , s)
    transition1 = IF-TRUEₛₛₛ (GREATERTHAN-1-BSS NUM-BSS (VAR-BSS refl) (+<+ s≤s s≤s s≤s s≤s z≤n)) ⇒∘⇒* x⇒x , refl

    -- There's only one transition from the start state
    f : s ⊢ inj₁ (inj₁ (N + 3) + inj₁ (V "x")) ⇒ₐ inj₂ (+ 7)
    f = NUM-BSS PLUS-BSS (VAR-BSS refl)
    transition2 :
        inj₁ (
            ("x" ←₂ inj₁(inj₁(N + 3) + inj₁(V "x"))) Å₂
            ("y" ←₂ inj₁(N + 4))
            , s
        )
        ⇒⟨ 1 ⟩
        inj₁ (
            ("y" ←₂ inj₁(N + 4))
            , (s [ "x" ↦ + 7 ])
        )
    transition2 = COMP-2ₛₛₛ (ASSₛₛₛ (NUM-BSS PLUS-BSS (VAR-BSS refl))) ⇒∘⇒* x⇒x , refl

    transition3 :
        inj₁ (
            ("y" ←₂ inj₁(N + 4))
            , (s [ "x" ↦ + 7 ])
        )
        ⇒⟨ 1 ⟩
        inj₂ (
            s [ "x" ↦ + 7 ] [ "y" ↦ + 4 ]
        )
    transition3 = ASSₛₛₛ NUM-BSS ⇒∘⇒* x⇒x , refl

-- Section End Page 54

-- Section Begin Page 55-58

module SmallStep-BigStep-Equivalence where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    import Bims
    open Bims.Aexp₂-semantic
    open Bims.Stm₂-semantic hiding (<<str)
    open import Data.Nat using (ℕ; suc; zero) renaming (_+_ to _+ℕ_)
    open import Data.Integer using (+_)
    open import Data.String using (String)
    open import Data.Product using (_×_; _,_; Σ; ∃; proj₁; proj₂)
    open import Data.Sum using (inj₁; inj₂)
    open import Data.Bool using (false; true)
    open import TransitionSystems using () renaming (TransitionSystem to T)
    open T ⟨_⟩⇒₂⟨_⟩-transition using (x⇒x; _⇒⟨_⟩_; _⇒∘⇒*_; _⇒*_; _∘⇒*∘_; _⇒_; length)

    open import Data.Integer using (ℤ; +_)
    open import Data.String using (String; _<?_) renaming (_==_ to _==s_; _<_ to _<s_)
    open import States ℤ String _<s_ <<str _<?_ _==s_

    L4-12 : {S₁ S₂ : Stm₂} {s s´ : States}
          → inj₁(S₁ , s) ⇒* inj₂ s´
          → inj₁(S₁ Å₂ S₂ , s) ⇒* inj₁(S₂ , s´)
    L4-12 (fst₁ ⇒∘⇒* x⇒x) = COMP-2ₛₛₛ fst₁ ⇒∘⇒* x⇒x
    L4-12 (_⇒∘⇒*_ {j = inj₁ S₁´,s˝} premise⟨S₁,s⟩⇒⟨S₁´,s˝⟩ ⟨S₁´,s˝⟩⇒*y) = COMP-1ₛₛₛ premise⟨S₁,s⟩⇒⟨S₁´,s˝⟩ T.⇒∘⇒* L4-12 ⟨S₁´,s˝⟩⇒*y

    -- Theorem 4.11 -- Apparently this should be hard to prove, and needs the lemma, though agda figures it out without the lemma
    T4-11 : {S : Stm₂} → {s s´ : States} → ⟨ S , s ⟩⇒₂ s´ → inj₁(S , s) ⇒* inj₂ s´
    T4-11 (ASS-BSS x) = ASSₛₛₛ x ⇒∘⇒* x⇒x
    T4-11 SKIP-BSS = SKIPₛₛₛ ⇒∘⇒* x⇒x
    T4-11 (COMP-BSS ⟨S₁,s⟩⇒s´ ⟨S₂,s´⟩⇒s˝) = L4-12 (T4-11 ⟨S₁,s⟩⇒s´) ∘⇒*∘ T4-11 ⟨S₂,s´⟩⇒s˝
    T4-11 (IF-TRUE-BSS x x₁) =  IF-TRUEₛₛₛ x₁ ⇒∘⇒* T4-11 x
    T4-11 (IF-FALSE-BSS x x₁) = IF-FALSEₛₛₛ x₁ ⇒∘⇒* T4-11 x
    T4-11 (WHILE-TRUE-BSS s⊢b⇒ᵇtt ⟨S,s⟩⇒s˝ ⟨while-b-do-S,s˝⟩⇒s´) = WHILEₛₛₛ ⇒∘⇒* IF-TRUEₛₛₛ s⊢b⇒ᵇtt ⇒∘⇒* L4-12 (T4-11 ⟨S,s⟩⇒s˝) ∘⇒*∘ T4-11 ⟨while-b-do-S,s˝⟩⇒s´
    T4-11 (WHILE-FALSE-BSS s⊢b⇒ᵇff) = WHILEₛₛₛ ⇒∘⇒* IF-FALSEₛₛₛ s⊢b⇒ᵇff ⇒∘⇒* SKIPₛₛₛ ⇒∘⇒* x⇒x

    open import Relation.Binary.PropositionalEquality using (cong; trans)
    L4-14 : {S₁ S₂ : Stm₂} {s s˝ : States}
          → (t : inj₁(S₁ Å₂ S₂ , s) ⇒* inj₂ s˝)
          → ∃ λ s´ →
            Σ (inj₁(S₁ , s ) ⇒* inj₂ s´) λ lSeq →
            Σ (inj₁(S₂ , s´) ⇒* inj₂ s˝) λ rSeq →
            length t ≡ length lSeq +ℕ length rSeq
    L4-14 (COMP-1ₛₛₛ x ⇒∘⇒* x₁) =
        L4-14 x₁ .proj₁ ,
        x ⇒∘⇒* L4-14 x₁ .proj₂ .proj₁ ,
        L4-14 x₁ .proj₂ .proj₂ .proj₁ ,
        cong suc (L4-14 x₁ .proj₂ .proj₂ .proj₂)
    L4-14 (COMP-2ₛₛₛ x ⇒∘⇒* x₁) = _ , x ⇒∘⇒* x⇒x , x₁ , refl

    step-then-big : {S S´ : Stm₂} {s s´ s˝ : States}
                  → inj₁(S , s) ⇒ inj₁(S´ , s´)
                  → ⟨ S´ , s´ ⟩⇒₂ s˝
                  → ⟨ S , s ⟩⇒₂ s˝
    step-then-big (COMP-1ₛₛₛ x) (COMP-BSS y y₁) = COMP-BSS (step-then-big x y) y₁
    step-then-big (COMP-2ₛₛₛ (ASSₛₛₛ x)) y = COMP-BSS (ASS-BSS x) y
    step-then-big (COMP-2ₛₛₛ SKIPₛₛₛ) y = COMP-BSS SKIP-BSS y
    step-then-big (IF-TRUEₛₛₛ x) y = IF-TRUE-BSS y x
    step-then-big (IF-FALSEₛₛₛ x) y = IF-FALSE-BSS y x
    step-then-big WHILEₛₛₛ (IF-TRUE-BSS (COMP-BSS y y₁) x) = WHILE-TRUE-BSS x y y₁
    step-then-big WHILEₛₛₛ (IF-FALSE-BSS SKIP-BSS x) = WHILE-FALSE-BSS x

    -- Theorem 4.13
    T4-13 : {S : Stm₂} {s s´ : States}
          → inj₁(S , s) ⇒* inj₂ s´
          → ⟨ S , s ⟩⇒₂ s´
    T4-13 (ASSₛₛₛ x ⇒∘⇒* x⇒x) = ASS-BSS x
    T4-13 (SKIPₛₛₛ ⇒∘⇒* x⇒x) = SKIP-BSS
    T4-13 (COMP-1ₛₛₛ ⟨S₁,s⟩⇒₂⟨S₁´,s´⟩  ⇒∘⇒*  ⟨S₁´:S₂,s´⟩⇒s´₁) with T4-13 ⟨S₁´:S₂,s´⟩⇒s´₁
    ... | COMP-BSS ⟨S₁´,s₁´⟩⇒s˝ ⟨S₂,s˝⟩⇒s´ = COMP-BSS (step-then-big ⟨S₁,s⟩⇒₂⟨S₁´,s´⟩ ⟨S₁´,s₁´⟩⇒s˝) ⟨S₂,s˝⟩⇒s´

    T4-13 (COMP-2ₛₛₛ (ASSₛₛₛ x) ⇒∘⇒* snd) = COMP-BSS (ASS-BSS x) (T4-13 snd)
    T4-13 (COMP-2ₛₛₛ SKIPₛₛₛ ⇒∘⇒* snd) = COMP-BSS SKIP-BSS (T4-13 snd)
    T4-13 (IF-TRUEₛₛₛ x ⇒∘⇒* snd) = IF-TRUE-BSS (T4-13 snd) x
    T4-13 (IF-FALSEₛₛₛ x ⇒∘⇒* snd) = IF-FALSE-BSS (T4-13 snd) x

    T4-13 (WHILEₛₛₛ ⇒∘⇒* IF-TRUEₛₛₛ x ⇒∘⇒* snd) with T4-13 snd
    ... | COMP-BSS a b = WHILE-TRUE-BSS x a b
    T4-13 (WHILEₛₛₛ ⇒∘⇒* IF-FALSEₛₛₛ x ⇒∘⇒* SKIPₛₛₛ ⇒∘⇒* x⇒x) = WHILE-FALSE-BSS x


-- Section End Page 55-58
