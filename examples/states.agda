module examples.states where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Fresh using (_∷#_; [])

open import Data.Integer using (ℤ; +_)
open import Data.String using (String; _<_; _<?_; _==_)
<<str = λ a b c → <-isStrictPartialOrder-≈ .trans {a} {b} {c}
    where
        open import Relation.Binary.Structures using (IsStrictPartialOrder)
        open IsStrictPartialOrder using (trans)
        open import Data.String.Properties using (<-isStrictPartialOrder-≈)
open import States ℤ String _<_ <<str _<?_ _==_

p1 : [] [ "hi" ↦ + 3 ] ≡ (( "hi" , + 3) ∷# [])
p1 = refl

p2 : ([] [ "hi" ↦ + 3 ] [ "yo" ↦ + 4 ]) ≡ (( "hi" , + 3) ∷# ( "yo" , + 4) ∷# [])
p2 = refl

p3 : [] [ "hi" ↦ + 3 ] [ "yo" ↦ + 4 ] ≡ [] [ "yo" ↦ + 4 ] [ "hi" ↦ + 3 ]
p3 = refl

a : States
a = ( "a" , + 0) ∷# ( "b" , + 0) ∷# []

p4 : a [ "a" ↦ + 0 ] ≡ a
p4 = refl
