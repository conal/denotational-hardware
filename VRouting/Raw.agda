{-# OPTIONS --safe --without-K #-}

module VRouting.Raw {A : Set} where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Function using (case_of_)

open import Data.Sum using ([_,_])

open import Categorical.Raw
open import Functions.Raw

open import Vector.Raw {A} hiding (_⇨_)

open import VRouting.Type {A} public

module vrouting-raw-instances where

  instance

    category : Category _⇨_
    category = record
      { id  = mk (allFin _)
      ; _∘_ = λ (mk g) (mk f) → mk (map (lookup f) g)
      }

    cartesian : Cartesian _⇨_
    cartesian = record
      { !   = mk []
      ; _▵_ = λ (mk f) (mk g) → mk (f ++ g)
      ; exl = mk (tabulate (inject+ _))
      ; exr = mk (tabulate ( raise  _))
      }
