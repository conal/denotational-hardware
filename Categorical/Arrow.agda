{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category; Cartesian)
open import Categorical.Homomorphism

module Categorical.Arrow
   {o}{obj : Set o} ⦃ _ : Products obj ⦄
   {ℓ} (_⇨_ : obj → obj → Set ℓ) ⦃ _ : Cartesian _⇨_ ⦄
   {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄
 where

private
  instance

    Hₒ : Homomorphismₒ obj obj
    Hₒ = id-Hₒ

    H : Homomorphism _⇨_ _⇨_
    H = id-H

    catH : CategoryH _⇨_ _⇨_
    catH = id-CategoryH

    prodH : ProductsH obj _⇨_
    prodH = id-ProductsH

    cartH : CartesianH _⇨_ _⇨_
    cartH = id-CartesianH

    -- TODO: Replace Hₒ, H, etc by a bundle

-- open import Categorical.Comma.Type _⇨_ _⇨_ _⇨_ ⦃ ch₁ = catH ⦄ ⦃ ch₂ = catH ⦄ public

open import Categorical.Comma.Raw _⇨_ _⇨_ _⇨_
  ⦃ catH₁ = catH ⦄ ⦃ cartH₁ = cartH ⦄
  ⦃ catH₂ = catH ⦄ ⦃ cartH₂ = cartH ⦄
  public
