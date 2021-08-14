{-# OPTIONS --safe --without-K #-}

module Routing.Type where

open import Level using (0ℓ)
open import Data.Empty
open import Data.Sum
open import Data.Product using (_,_)

open import Categorical.Raw
open import Categorical.Equiv
open import Functions.Raw
-- open import Fun.Type renaming (_⇨_ to _⇨ₜ_)

open import Ty
open import Index

private
  variable
    a b : Ty
    h : Ty → Set

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set where
  constructor mk
  field
    unMk : Swizzle a b

open _⇨_ public

⟦_⟧′ : a ⇨ b → Indexed h a → Indexed h b
⟦_⟧′ = swizzle′ ∘ unMk
-- ⟦ mk f ⟧′ = swizzle′ f

instance

  homomorphism : Homomorphism _⇨_ Function
  homomorphism = record { Fₘ = swizzle ∘ unMk }
  -- homomorphism = record { Fₘ = λ (mk r) → swizzle r }

  -- TODO: Generalize routing to any target category with Ty as objects. Later
  -- to any Cartesian category.

