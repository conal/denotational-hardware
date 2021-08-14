{-# OPTIONS --safe --without-K #-}

module Routing.Homomorphism {A : Set} where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Vec.Properties

open import Categorical.Laws
open import Categorical.Homomorphism

open import Functions.Raw
open import Functions.Laws
open import Vector.Laws {A} renaming (_⇨_ to _↠_)

open import Routing.Swizzle
open import Routing.Swizzle.Properties
open import Routing.Raw {A} public ; open _⇨_

module vrouting-homomorphism-instances where

  instance

    categoryH : CategoryH _⇨_ _↠_
    categoryH = record
      { F-id = swizzle-allFin
      ; F-∘  = λ { {g = mk g} {mk f} → swizzle-swizzle g f }
      }

    pH : ProductsH ℕ _↠_
    pH = id-ProductsH

    cartesianH : CartesianH _⇨_ _↠_
    cartesianH = record
      { F-!   = swizzle-[]
      ; F-exl = swizzle-tabulate-inject+
      ; F-exr = swizzle-tabulate-raise
      ; F-▵   = λ { {f = mk f}{mk g} → swizzle-++ f g }
      }

