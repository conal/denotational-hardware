{-# OPTIONS --safe --without-K #-}

module Routing.Type {A : Set} where

open import Data.Nat
open import Data.Fin
open import Data.Vec

open import Categorical.Raw
open import Categorical.Equiv
open import Functions.Raw
open import Vector.Type {A} renaming (_⇨_ to _↠_)

private
  variable
    m n : ℕ

open import Routing.Swizzle

infix 0 _⇨_
record _⇨_ (m n : ℕ) : Set where
  constructor mk
  field
    unMk : Swizzle m n


module vrouting-instances where

  instance

    H : Homomorphism _⇨_ _↠_
    H = record { Fₘ = mk ∘ swizzle ∘ unMk } where open _⇨_

    equivalent : Equivalent _ _⇨_
    equivalent = H-equiv H
