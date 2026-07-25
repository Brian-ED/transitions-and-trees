module examples.exampleExprs where
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_,_)
open import TransitionSystems using () renaming (TransitionSystem to T)
open import Data.Sum using (inj₁; inj₂)
import Bims
import examples.bims

-- Section Start Page 38. This label is place 1
-- page 28 is also done in TransitionSystems.agda

open Bims.Aexp₁-smallstep-semantic hiding (_⇒⟨_⟩_; _⇒*_; _⇒∘⇒_; x⇒x)
open T (examples.bims.Aexp₁-small-step-semantic.Aexp₁ssSemantic)

exampleAexp₂1 : ((N + 3 + N + 12) * (N + 4 * (N + 5 * N + 9)))
         ⇒⟨ 3 ⟩ (V + 15 * (N + 4 * (N + 5 * N + 9)))
exampleAexp₂1 = (MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ)
            ⇒∘⇒ (MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ)
            ⇒∘⇒ (MULT-1ₛₛₛ PLUS-3ₛₛₛ)
            ⇒∘⇒ x⇒x

-- Problem 3.12
exampleAexp₂2 : ((N + 2 + N + 3) * (N + 4 + N + 9)) ⇒* V + 65
exampleAexp₂2 = 7 , (MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ)
                ⇒∘⇒ (MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ)
                ⇒∘⇒ (MULT-1ₛₛₛ PLUS-3ₛₛₛ)
                ⇒∘⇒ (MULT-2ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ)
                ⇒∘⇒ (MULT-2ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ)
                ⇒∘⇒ (MULT-2ₛₛₛ PLUS-3ₛₛₛ)
                ⇒∘⇒ (MULT-3ₛₛₛ)
                ⇒∘⇒ x⇒x

-- Section End Page 38
