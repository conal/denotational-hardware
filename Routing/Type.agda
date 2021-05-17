{-# OPTIONS --safe --without-K #-}

module Routing.Type where

open import Level using (0ℓ)
open import Data.Empty
open import Data.Sum
open import Data.Product using (_,_)

open import Categorical.Raw
open import Functions.Raw 0ℓ

open import Ty
open import Log

private variable a b c d : Ty

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set where
  constructor mk
  field
    f : Log b → Log a

instance

  homomorphism : Homomorphism _⇨_ Function
  homomorphism = record { Fₘ = λ (mk r) → λ x → tabulate (lookup x ∘ r) }

  -- TODO: Generalize routing to any target category with Ty as objects. Later
  -- to any Cartesian category.

