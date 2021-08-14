{-# OPTIONS --safe --without-K #-}

module Routing.Raw where

open import Level using (0ℓ)
open import Data.Product using (_,_)
import Data.Sum as ⊎
open ⊎
open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)

open import Categorical.Raw
open import Functions.Raw

open import Ty
open import Index
open import Routing.Type public

instance

  category : Category _⇨_
  category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (f ∘ g) }

  cartesian : Cartesian _⇨_
  cartesian = record
    { !   = mk λ ()
    ; _▵_ = λ (mk f) (mk g) → mk λ { (left i) → f i ; (right j) → g j }
    ; exl = mk left
    ; exr = mk right
    }
