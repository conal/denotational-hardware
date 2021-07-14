{-# OPTIONS --safe --without-K #-}

module Categorical.Object where

open import Level using (Level; lift; _⊔_) renaming (suc to lsuc)
open import Function

open import Data.Nat hiding (_⊔_; _+_)

private
  variable
    o : Level
    obj : Set o

  -- Iterated composition
  infixr 8 _↑_
  _↑_ : ∀ {a}{A : Set a} → (A → A) → ℕ → (A → A)
  f ↑ zero  = id
  f ↑ suc n = f ∘ (f ↑ n)

record Products (obj : Set o) : Set (lsuc o) where
  infixr 2 _×_
  field
    ⊤ : obj
    _×_ : obj → obj → obj

  -- (Right-pointing) vectors and (perfect binary leaf) trees
  V T : obj → ℕ → obj
  V A n = ((A ×_) ↑ n) ⊤
  T A n = ((λ z → z × z) ↑ n) A

open Products ⦃ … ⦄ public

record CoProducts (obj : Set o) : Set (lsuc o) where
  infixr 2 _+_
  field
    ⊥ : obj
    _+_ : obj → obj → obj

open CoProducts ⦃ … ⦄ public

record Exponentials (obj : Set o) : Set (lsuc o) where
  infixr 1 _⇛_
  field
    _⇛_ : obj → obj → obj

open Exponentials ⦃ … ⦄ public


record Boolean (obj : Set o) : Set (lsuc o) where
  field
    Bool : obj

open Boolean ⦃ … ⦄ public
