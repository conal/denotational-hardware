{-# OPTIONS --safe --without-K #-}

-- open import Data.Product using (_,_)
-- open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)

module VRouting.Homomorphism {A : Set} where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Vec.Properties

open import Categorical.Laws
open import Categorical.Homomorphism

open import Functions.Raw
open import Functions.Laws
open import Vector.Laws {A} renaming (_⇨_ to _↠_)
open import VRouting.Raw {A} public ; open _⇨_
open import VRouting.Swizzle ; open swizzle-laws

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

