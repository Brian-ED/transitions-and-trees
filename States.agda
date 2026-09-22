open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Data.Bool using (if_then_else_; Bool; false; true; _∧_)
open import Data.Product using (∃; Σ; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Maybe using (Maybe; just; map)
open import Relation.Nullary using (yes; no)
open import Data.List using (findᵇ; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nary using (⌊_⌋)
open import Data.List.Fresh using (List#; cons; []; _∷#_; fresh; toList)
open import Function using (_∘_)

import Level

module States
    {ℓ₁} {ℓ₂}
    (𝕍 : Set ℓ₁)
    (ID : Set ℓ₂)
    (_<_ : Rel ID ℓ₂)
    (<<ID : ∀ a b c → a < b → b < c → a < c ) -- takes explicit args because calling a module with a func as arg that takes implicit args errors as Agda doesn't always match them correctly
    (_<?_ : Decidable _<_)
    (_==_ : ID → ID → Bool)
    where

_<<_ = λ {a} {b} {c} → <<ID a b c

cmp : (a : ID × 𝕍) → (b : ID × 𝕍) → Relation.Nullary.Dec (a .proj₁ < b .proj₁)
cmp (a , b) (x , y) = a <? x

States = List# {r = ℓ₂} {a = ℓ₁ Level.⊔ ℓ₂} (ID × 𝕍) ⌊ cmp ⌋

toDec : ∀ {s₁ s} → s₁ < s → ⌊ s₁ <? s ⌋
toDec {s₁} {s} x .Level.lower with s₁ <? s
... | yes p = _
... | no p = p x

fromDec : ∀ {id} {id₁} → ⌊ id <? id₁ ⌋ → id < id₁
fromDec {id} {id₁} _ with id <? id₁
fromDec _ | yes p = p

appendFresh : ∀ {s n id val xs₁} x → s < id → fresh (ID × 𝕍) ⌊ cmp ⌋ (s , n) (cons (id , val) xs₁ x)
appendFresh {xs₁ = []} _ ordered = toDec ordered , _
appendFresh {xs₁ = cons (id₁ , val₁) xs₁ lower} (lower₁ , snd₁) ordered = toDec ordered , appendFresh lower (ordered << fromDec lower₁)

_[_↦_] : (s : States) → (id : ID) → (v : 𝕍) → States
[] [ id ↦ v ] = (id , v) ∷# []
cons (id₁ , _) _ _ [ id ↦ _ ] with id <? id₁ | id₁ <? id
cons s₁ [] _ [ id ↦ v ] | yes p | _ = cons (id , v) (s₁ ∷# []) (toDec p , _)
cons s₁ [] _ [ id ↦ v ] | no  _ | yes q = cons s₁ ((id , v) ∷# []) (toDec q , _)
cons s₁ [] _ [ id ↦ v ] | no  _ | no  q = (id , v) ∷# []
cons s₁ s p₁ [ id ↦ v ] | yes p | _ = cons (id , v) (cons s₁ s p₁) (appendFresh p₁ p)
cons (id₁ , _ ) (cons (id₂ , v₂) s p₂) p₁ [ id ↦ v ] | no p | no  q = cons (id₁ , v) (cons (id₂ , v₂) s p₂) (appendFresh p₂ (fromDec (proj₁ p₁)))
cons (id₁ , v₁) (cons (id₂ , v₂) s p₂) p₁ [ id ↦ v ] | no p | yes q
    with (cons (id₂ , v₂) s p₂) [ id ↦ v ]
... | [] = (id₁ , v₁) ∷# [] -- TODO The recursive case can never give empty so this case should be proven impossible
... | cons (idᵣ₁ , vᵣ₁) r pᵣ₁ with id₁ <? idᵣ₁ -- TODO Should always be true since recursive case can only ever put an element higher than id₁ at first index, but I wasn't able to prove it
... | yes pp = cons (id₁ , v₁) (cons (idᵣ₁ , vᵣ₁) r pᵣ₁) (appendFresh pᵣ₁ pp)
... | no  pp = [] -- See comment 2 lines above

lookup : States → ID → Maybe 𝕍
lookup xs id = map proj₂ (findᵇ (id ==_ ∘ proj₁) (toList xs .proj₁))

joinOverwrite : (overWritee overWriter : States) → States
joinOverwrite overWritee overWriter = foldr (λ x y → uncurry (y [_↦_]) x) overWritee (toList overWriter .proj₁)

_⊢_==ₛ_ : (_==ᵥ_ : 𝕍 → 𝕍 → Bool) → States → States → Bool
_ ⊢ [] ==ₛ [] = true
_ ⊢ [] ==ₛ _  = false
_ ⊢ _  ==ₛ [] = false
_==ᵥ_ ⊢ (aID , aV) ∷# as ==ₛ ((bID , bV) ∷# bs) = (aV ==ᵥ bV) ∧ (aID == bID) ∧ (_==ᵥ_ ⊢ as ==ₛ bs)

delete : (id : ID) → (s : States) → (∃ λ v → lookup s id ≡ just v) → States
delete id ((id₁ , v₁) ∷# xs) z with id == id₁
... | true = xs
... | false = delete id xs z [ id₁ ↦ v₁ ]
