{-# OPTIONS --safe --without-K #-}

module VRouting.Laws {A : Set} where

open import Categorical.Raw
import Categorical.Laws as L
open import Categorical.MakeLawful

open import Vector.Laws {A} renaming (_⇨_ to _↠_)
open import VRouting.Homomorphism {A} public

-- Inherit lawfulness from vector functions

module vrouting-laws-instances where

  instance

    category : L.Category _⇨_
    category = LawfulCategoryᶠ _↠_
