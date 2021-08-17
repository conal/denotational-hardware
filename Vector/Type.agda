{-# OPTIONS --safe --without-K #-}

module Vector.Type {A : Set} where

open import Data.Product using (_,_)

open import Categorical.Raw
open import Categorical.Homomorphism
open import Functions.Raw

open import Data.Nat
open import Data.Vec

infixr 1 _⇨_
record _⇨_ (m n : ℕ) : Set where
  constructor mk
  field
    unMk : Vec A m → Vec A n

module vector-instances where

  instance

    Hₒ-id : Homomorphismₒ ℕ ℕ
    Hₒ-id = id-Hₒ

    Hₒ : Homomorphismₒ ℕ Set
    Hₒ = record { Fₒ = Vec A }

    H : Homomorphism _⇨_ Function
    H = record { Fₘ = unMk } where open _⇨_

    equivalent : Equivalent _ _⇨_
    equivalent = H-equiv H


app : ∀ {m n : ℕ} → Vec A m × Vec A n → Vec A (m + n)
app (u , v) = u ++ v

app⁻¹ : ∀ {m n : ℕ} → Vec A (m + n) → Vec A m × Vec A n
app⁻¹ {m} = take m ▵ drop m
