{-# OPTIONS --safe --without-K #-}

module VRouting.Swizzle where

open import Data.Nat
open import Data.Fin
open import Data.Vec

Swizzle : ℕ → ℕ → Set
Swizzle m n = Vec (Fin m) n

swizzle : ∀ {A : Set}{m}{n} → Swizzle m n → Vec A m → Vec A n
swizzle s xs = map (lookup xs) s
