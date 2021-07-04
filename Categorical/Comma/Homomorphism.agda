{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category; Cartesian)
open import Categorical.Homomorphism

module Categorical.Comma.Homomorphism
   {o₁}{obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄
     {ℓ₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Cartesian _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
     {ℓ₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Cartesian _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} ⦃ _ : Products obj₃ ⦄
     {ℓ₃} (_⇨₃_ : obj₃ → obj₃ → Set ℓ₃) ⦃ _ : Cartesian _⇨₃_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₁_ ⦄ ⦃ _ : L.Cartesian _⇨₁_ ⦄
       ⦃ _ : Equivalent q _⇨₂_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
       ⦃ _ : Equivalent q _⇨₃_ ⦄ ⦃ _ : L.Cartesian _⇨₃_ ⦄
   ⦃ _ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₁_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₁_ _⇨₃_ ⦄ ⦃ _ : ProductsH obj₁ _⇨₃_ ⦄
     ⦃ _ : CartesianH _⇨₁_ _⇨₃_ ⦄
   ⦃ _ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₂_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₂_ _⇨₃_ ⦄ ⦃ _ : ProductsH obj₂ _⇨₃_ ⦄
     ⦃ _ : CartesianH _⇨₂_ _⇨₃_ ⦄
 where

open import Categorical.Comma.Raw _⇨₁_ _⇨₂_ _⇨₃_ public

module comma-homomorphism-instances where

  instance

    open import Categorical.Homomorphism

    categoryH₁ : CategoryH _⇨_ _⇨₁_
    categoryH₁ = record { F-id = refl ; F-∘ = refl }

    categoryH₂ : CategoryH _⇨_ _⇨₂_
    categoryH₂ = record { F-id = refl ; F-∘ = refl }

    -- Also CartesianH, CartesianClosedH, and LogicH
