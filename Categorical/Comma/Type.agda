{-# OPTIONS --safe --without-K #-}
-- Comma categories

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Homomorphism

module Categorical.Comma.Type
   {o₁}{obj₁ : Set o₁} {ℓ₁}(_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ c₁ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂}(_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ c₂ : Category _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} {ℓ₃}(_⇨₃_ : obj₃ → obj₃ → Set ℓ₃) ⦃ c₃ : Category _⇨₃_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₃_ ⦄
   ⦃ hₒ₁ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ h₁ : Homomorphism _⇨₁_ _⇨₃_ ⦄
     ⦃ catH₁ : CategoryH _⇨₁_ _⇨₃_ ⦄
   ⦃ hₒ₂ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ h₂ : Homomorphism _⇨₂_ _⇨₃_ ⦄
     ⦃ catH₂ : CategoryH _⇨₂_ _⇨₃_ ⦄
 where

-- TODO: Define some bundles to reduce syntactic clutter.

record Obj : Set (o₁ ⊔ o₂ ⊔ ℓ₃) where
  constructor mk
  field
    { τ₁ } : obj₁
    { τ₂ } : obj₂
    h : Fₒ τ₁ ⇨₃ Fₒ τ₂

open Obj

infix 0 _⇨_
record _⇨_ (a : Obj) (b : Obj) : Set (q ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor mk
  field
    f₁ : τ₁ a ⇨₁ τ₁ b
    f₂ : τ₂ a ⇨₂ τ₂ b
    commute : h b ∘ Fₘ f₁ ≈ Fₘ f₂ ∘ h a

open _⇨_

-- Shorthand
infix 0 _⇉_
_⇉_ : ∀ {σ₁ τ₁ : obj₁}{σ₂ τ₂ : obj₂}
    → (Fₒ σ₁ ⇨₃ Fₒ σ₂) → (Fₒ τ₁ ⇨₃ Fₒ τ₂) → Set (ℓ₁ ⊔ ℓ₂ ⊔ q)
g ⇉ h = mk g ⇨ mk h

module comma-type-instances where

  open import Categorical.Equiv

  instance
  
    -- Forgetful functors

    homomorphismₒ₁ : Homomorphismₒ Obj obj₁
    homomorphismₒ₁ = record { Fₒ = τ₁ }

    homomorphism₁ : Homomorphism _⇨_ _⇨₁_
    homomorphism₁ = record { Fₘ = _⇨_.f₁ }

    homomorphismₒ₂ : Homomorphismₒ Obj obj₂
    homomorphismₒ₂ = record { Fₒ = τ₂ }

    homomorphism₂ : Homomorphism _⇨_ _⇨₂_
    homomorphism₂ = record { Fₘ = _⇨_.f₂ }
