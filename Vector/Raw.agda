{-# OPTIONS --safe --without-K #-}

module Vector.Raw {A : Set} where

open import Data.Nat
open import Data.Vec

open import Categorical.Raw
open import Categorical.Equiv
open import Functions

open import Vector.Type {A} public

module vec-raw-instances where

  instance

    category : Category _⇨_
    category = record
      { id  = mk id
      ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f)
      }

    products : Products ℕ
    products = record { ⊤ = zero ; _×_ = _+_ }

    cartesian : Cartesian _⇨_
    cartesian =
      record
        { !   = mk (λ _ → [])
        ; _▵_ = λ (mk f) (mk g) → mk (λ xs → f xs ++ g xs)
        ; exl = mk (take _)
        ; exr = mk (drop _)
        }
