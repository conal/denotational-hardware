{-# OPTIONS --safe --without-K #-}

module Vector.Laws {A : Set} where

open import Categorical.Raw
import Categorical.Laws as L
open import Categorical.MakeLawful

open import Functions
open import Vector.Homomorphism {A} public

-- Inherit lawfulness from functions

module vector-laws-instances where

  instance

    category : L.Category _⇨_
    category = LawfulCategoryᶠ Function
